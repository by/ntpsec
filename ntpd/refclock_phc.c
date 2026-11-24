/*
 * refclock_phc - clock driver for Linux PTP Hardware Clocks (/dev/ptpN)
 *
 * Copyright the NTPsec project contributors
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * A PTP Hardware Clock (PHC) is a clock living on a network card or
 * other device.  It is typically kept synchronized to a PTP grandmaster
 * by ptp4l, or to a GNSS receiver's PPS output by ts2phc.  The driver
 * has two modes.
 *
 * Offset mode (default)
 * ---------------------
 * Once per second the driver measures the offset between the PHC and
 * the system clock (CLOCK_REALTIME) and feeds it to the refclock
 * filter.  A reading is a burst of samples, each a PHC timestamp
 * bracketed by two system timestamps, taken with the best method the
 * device offers:
 *
 *   1. PTP_SYS_OFFSET_PRECISE  - hardware cross-timestamp (Intel
 *                                ART/PCIe PTM); a single exact pair.
 *   2. PTP_SYS_OFFSET_EXTENDED - the NIC driver brackets each PHC
 *                                register read with system timestamps.
 *   3. PTP_SYS_OFFSET          - older kernel interface.
 *   4. clock_gettime() on the dynamic POSIX clock, bracketed in user
 *      space.
 *
 * The best working method is chosen at startup; if it later fails with
 * "not supported" the driver falls back to the next one.
 *
 * Within a burst, samples with short brackets are the trustworthy
 * ones: a long bracket means the read was delayed (PCIe contention, an
 * interrupt, SMI) and the PHC timestamp could sit anywhere inside it.
 * Rather than keep only the single shortest bracket, the driver keeps a
 * running estimate of a low percentile of bracket widths across bursts
 * and averages every sample whose bracket falls at or below it.  That
 * cuts the read noise by roughly the square root of the number of
 * samples averaged, while still discarding the delayed ones.  A burst
 * in which any bracket is negative straddled a system clock step and
 * is thrown away whole.
 *
 * External PPS mode
 * -----------------
 * Many PHCs (Intel i210/i225/E810, Mellanox, ...) can timestamp edges
 * on an input pin.  Wire a GNSS receiver's PPS output there and the
 * PHC becomes a hardware PPS timestamper: no serial-port or interrupt
 * latency.  In this mode the PHC need not be synchronized to anything;
 * the per-second offset readings are used only to map PHC time onto
 * system time, and each pulse is turned into a sample of the system
 * clock's offset from the nearest whole second.  As with the pps
 * driver, another source must number the seconds, so samples are
 * discarded until ntpd is synchronized.
 *
 * Events are drained from the once-per-second timer rather than via
 * ntpd's I/O loop: the timestamps come from hardware, so prompt reads
 * gain nothing, and the PHC character device ignores O_NONBLOCK on
 * many kernels, which would hang the I/O loop's drain-until-empty
 * read.  Each read is guarded by a zero-timeout poll() instead.
 *
 * Configuration:
 *
 *   refclock phc unit N [path DEV] [mode M] [time1 OFFS]
 *                [flag1 1] [flag2 1] [flag4 1]
 *
 *   path	/dev/ptpX, or a network interface name such as eth0, in
 *		which case the interface's PHC is used; default
 *		/dev/ptp<unit>
 *   mode	bits 0-7   samples per reading, 1..25; 0 means 25
 *		bit 8      (256) external PPS mode
 *		bit 9      (512) timestamp falling instead of rising edges
 *		bit 10    (1024) don't configure the pin (fixed-function
 *		                 channel)
 *		bits 16-23       pin index for external PPS
 *		bits 24-31       channel index for external PPS
 *   time1	fixed offset added to every sample (seconds)
 *   flag1	the PHC runs on TAI (offset mode); subtract the current
 *		TAI-UTC offset from the leap second file, or failing
 *		that, from the kernel
 *   flag2	don't use hardware cross-timestamping
 *		(PTP_SYS_OFFSET_PRECISE)
 *   flag4	write per-poll statistics to clockstats
 *
 * Reference ID defaults to "PHC" ("PPS" in external PPS mode).
 *
 * In offset mode the driver trusts the PHC: it cannot tell whether
 * ptp4l/ts2phc actually has the device locked.  Monitor those daemons
 * separately.
 */

#include "config.h"
#include "ntp.h"
#include "ntpd.h"
#include "ntp_refclock.h"
#include "ntp_stdlib.h"
#include "ntp_syscall.h"
#include "ntp_leapsec.h"
#include "timespecops.h"

#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <poll.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <net/if.h>
#include <linux/ethtool.h>
#include <linux/sockios.h>
#include <linux/ptp_clock.h>

/*
 * Interface definitions
 */
#define NAME		"PHC"		/* shortname */
#define DESCRIPTION	"PTP Hardware Clock"
#define REFID		"PHC"		/* default reference ID */
#define REFID_PPS	"PPS"		/* reference ID, external PPS mode */
#define DEVICE		"/dev/ptp%d"	/* default device name */
#define PRECISION	(-20)		/* initial guess, about 1 us */

#ifndef PTP_MAX_SAMPLES
# define PTP_MAX_SAMPLES 25
#endif
#define MAX_SAMPLES	PTP_MAX_SAMPLES
#define DEF_SAMPLES	MAX_SAMPLES	/* the burst is cheap; use it all */

#define MAX_DELAY_NS	1000000		/* reject brackets over 1 ms */
#define BAND_FLOOR_NS	20		/* never make the band narrower */
#define DELAY_PCTILE	0.2		/* percentile tracked */
#define NS_PER_SEC	1000000000LL

/* mode word */
#define MODE_SAMPLES(m)	((m) & 0xffu)
#define MODE_EXTPPS	0x100u
#define MODE_FALLING	0x200u
#define MODE_NOPIN	0x400u
#define MODE_PIN(m)	(((m) >> 16) & 0xffu)
#define MODE_CHANNEL(m)	(((m) >> 24) & 0xffu)

/* external PPS */
#define MODEL_MAX_AGE	(4 * NS_PER_SEC) /* readings older are useless */
#define MIN_PULSE_GAP	(NS_PER_SEC / 2) /* reject the other edge */
#define EXTTS_BATCH	8		/* events per read() */
#define EXTTS_MAX_READS	16		/* reads per timer tick */

/* Turn an open /dev/ptpN descriptor into a dynamic POSIX clock id. */
#define FD_TO_CLOCKID(fd)	((clockid_t)((((unsigned int)~(fd)) << 3) | 3))

enum phc_method {
	PHC_PRECISE = 0,	/* PTP_SYS_OFFSET_PRECISE */
	PHC_EXTENDED,		/* PTP_SYS_OFFSET_EXTENDED */
	PHC_BASIC,		/* PTP_SYS_OFFSET */
	PHC_READ,		/* clock_gettime() bracketed in user space */
	PHC_NMETHODS
};

static const char * const method_name[PHC_NMETHODS] = {
	"PTP_SYS_OFFSET_PRECISE",
	"PTP_SYS_OFFSET_EXTENDED",
	"PTP_SYS_OFFSET",
	"clock_gettime"
};

/* One sample: system time before, PHC time, system time after (ns). */
struct phc_sample {
	int64_t		sys1;
	int64_t		phc;
	int64_t		sys2;
};

struct phcunit {
	int		fd;		/* open /dev/ptpN */
	clockid_t	clkid;		/* dynamic POSIX clock id */
	enum phc_method method;		/* current measurement method */
	unsigned int	nsamples;	/* samples per reading */
	bool		tai_warned;	/* already complained about TAI */

	/* running low-percentile estimate of bracket width, ns */
	double		dq;
	bool		dq_valid;

	/* external PPS */
	bool		extpps;
	unsigned int	channel;
	int64_t		last_pulse;	/* PHC time of last accepted edge */
	int64_t		m_sys[2];	/* last two readings: system time */
	int64_t		m_off[2];	/* ... and PHC-minus-system offset */
	int		m_n;		/* how many of those are valid */

	/* tallies, reset at each poll */
	int		ticks;		/* readings attempted */
	int		good;		/* readings accepted */
	int		bad;		/* readings failed or rejected */
	int		used;		/* samples averaged, summed */
	int		pulses;		/* PPS edges accepted */
	int64_t		mindelay;	/* shortest bracket seen, ns */
};

/*
 * Function prototypes
 */
static	bool	phc_start	(int, struct peer *);
static	void	phc_shutdown	(struct refclockproc *);
static	void	phc_poll	(int, struct peer *);
static	void	phc_control	(int, const struct refclockstat *,
				 struct refclockstat *, struct peer *);
static	void	phc_timer	(int, struct peer *);
static	void	phc_drain_extts	(struct peer *, struct phcunit *);

/*
 * Transfer vector
 */
struct refclock refclock_phc = {
	NAME,		/* basename of driver */
	phc_start,	/* start up driver */
	phc_shutdown,	/* shut down driver */
	phc_poll,	/* transmit poll message */
	phc_control,	/* fudge control */
	NULL,		/* initialize driver (not used) */
	phc_timer,	/* called once per second */
};


/*
 * Nanosecond helpers.  int64_t ns since the epoch is good to 2262.
 */
static inline int64_t
pct_to_ns(const struct ptp_clock_time *t)
{
	return (int64_t)t->sec * NS_PER_SEC + (int64_t)t->nsec;
}

static inline int64_t
ts_to_ns(const struct timespec *t)
{
	return (int64_t)t->tv_sec * NS_PER_SEC + (int64_t)t->tv_nsec;
}

static inline struct timespec
ns_to_ts(int64_t ns)
{
	struct timespec ts;

	ts.tv_sec = (time_t)(ns / NS_PER_SEC);
	ts.tv_nsec = (long)(ns % NS_PER_SEC);
	if (ts.tv_nsec < 0) {
		ts.tv_nsec += 1000000000L;
		ts.tv_sec--;
	}
	return ts;
}

/* Precision exponent (log2 seconds) for a measurement uncertainty. */
static int8_t
ns_to_precision(int64_t ns)
{
	int8_t prec = -30;	/* 2^-30 s ~= 0.93 ns */
	double sec = (ns > 0 ? (double)ns : 1.0) / 1e9;

	while (prec < 0 && ldexp(1.0, prec) < sec) {
		prec++;
	}
	return prec;
}


/*
 * Raw readers.  Each fills s[] and returns the number of samples, or a
 * negative errno.
 */
static int
read_precise(struct phcunit *up, struct phc_sample *s)
{
#ifdef PTP_SYS_OFFSET_PRECISE
	struct ptp_sys_offset_precise pso;

	memset(&pso, 0, sizeof(pso));
	if (ioctl(up->fd, PTP_SYS_OFFSET_PRECISE, &pso) < 0) {
		return -errno;
	}
	s[0].phc = pct_to_ns(&pso.device);
	s[0].sys1 = s[0].sys2 = pct_to_ns(&pso.sys_realtime);
	return 1;
#else
	UNUSED_ARG(up); UNUSED_ARG(s);
	return -EOPNOTSUPP;
#endif
}

static int
read_extended(struct phcunit *up, struct phc_sample *s)
{
#ifdef PTP_SYS_OFFSET_EXTENDED
	struct ptp_sys_offset_extended pso;
	unsigned int i, n;

	memset(&pso, 0, sizeof(pso));	/* rsv[0] == 0: CLOCK_REALTIME */
	pso.n_samples = up->nsamples;
	if (ioctl(up->fd, PTP_SYS_OFFSET_EXTENDED, &pso) < 0) {
		return -errno;
	}
	n = pso.n_samples < up->nsamples ? pso.n_samples : up->nsamples;
	for (i = 0; i < n; i++) {
		s[i].sys1 = pct_to_ns(&pso.ts[i][0]);
		s[i].phc  = pct_to_ns(&pso.ts[i][1]);
		s[i].sys2 = pct_to_ns(&pso.ts[i][2]);
	}
	return (int)n;
#else
	UNUSED_ARG(up); UNUSED_ARG(s);
	return -EOPNOTSUPP;
#endif
}

static int
read_basic(struct phcunit *up, struct phc_sample *s)
{
#ifdef PTP_SYS_OFFSET
	struct ptp_sys_offset pso;
	unsigned int i, n;

	memset(&pso, 0, sizeof(pso));
	pso.n_samples = up->nsamples;
	if (ioctl(up->fd, PTP_SYS_OFFSET, &pso) < 0) {
		return -errno;
	}
	/* ts[] is sys, phc, sys, phc, ..., sys */
	n = pso.n_samples < up->nsamples ? pso.n_samples : up->nsamples;
	for (i = 0; i < n; i++) {
		s[i].sys1 = pct_to_ns(&pso.ts[2 * i]);
		s[i].phc  = pct_to_ns(&pso.ts[2 * i + 1]);
		s[i].sys2 = pct_to_ns(&pso.ts[2 * i + 2]);
	}
	return (int)n;
#else
	UNUSED_ARG(up); UNUSED_ARG(s);
	return -EOPNOTSUPP;
#endif
}

static int
read_gettime(struct phcunit *up, struct phc_sample *s)
{
	unsigned int i;

	for (i = 0; i < up->nsamples; i++) {
		struct timespec s1, p, s2;

		if (clock_gettime(CLOCK_REALTIME, &s1) < 0 ||
		    clock_gettime(up->clkid, &p) < 0 ||
		    clock_gettime(CLOCK_REALTIME, &s2) < 0) {
			return -errno;
		}
		s[i].sys1 = ts_to_ns(&s1);
		s[i].phc  = ts_to_ns(&p);
		s[i].sys2 = ts_to_ns(&s2);
	}
	return (int)up->nsamples;
}

static int
read_raw(struct phcunit *up, enum phc_method m, struct phc_sample *s)
{
	switch (m) {
	case PHC_PRECISE:
		return read_precise(up, s);
	case PHC_EXTENDED:
		return read_extended(up, s);
	case PHC_BASIC:
		return read_basic(up, s);
	case PHC_READ:
	case PHC_NMETHODS:
	default:
		return read_gettime(up, s);
	}
}


/*
 * Feed one bracket width into the running percentile estimate.  This
 * is the classic stochastic-approximation quantile tracker: nudge the
 * estimate up by p*step when the observation lies above it and down by
 * (1-p)*step when below, so it settles where a fraction p of
 * observations fall below.  The step scales with the estimate, which
 * makes convergence time independent of the absolute delay.
 */
static void
dq_update(struct phcunit *up, int64_t d)
{
	double step;

	if (!up->dq_valid) {
		up->dq = (double)d;
		up->dq_valid = true;
		return;
	}
	step = up->dq / 32.0;
	if (step < 1.0) {
		step = 1.0;
	}
	if ((double)d < up->dq) {
		up->dq -= step * (1.0 - DELAY_PCTILE);
	} else {
		up->dq += step * DELAY_PCTILE;
	}
	if (up->dq < 0.0) {
		up->dq = 0.0;
	}
}

/*
 * Reduce a burst to one (PHC, system) pair.  Returns the number of
 * samples combined, 0 if the burst must be discarded.
 */
static int
combine(struct phcunit *up, const struct phc_sample *s, int n,
	int64_t *phc_ns, int64_t *sys_ns, int64_t *delay_ns)
{
	int64_t dmin = INT64_MAX, hi, base;
	int64_t sum_mid = 0, sum_off = 0, sum_delay = 0;
	int i, used = 0;

	for (i = 0; i < n; i++) {
		int64_t d = s[i].sys2 - s[i].sys1;

		if (d < 0) {
			return 0;	/* system clock stepped mid-burst */
		}
		if (d < dmin) {
			dmin = d;
		}
	}
	if (n < 1 || dmin > MAX_DELAY_NS) {
		return 0;
	}

	for (i = 0; i < n; i++) {
		dq_update(up, s[i].sys2 - s[i].sys1);
	}
	hi = (int64_t)up->dq;
	if (hi < dmin + BAND_FLOOR_NS) {
		hi = dmin + BAND_FLOOR_NS;
	}

	/* sum relative to the first timestamp so 25 terms can't overflow */
	base = s[0].sys1;
	for (i = 0; i < n; i++) {
		int64_t d = s[i].sys2 - s[i].sys1;
		int64_t mid = s[i].sys1 + d / 2;

		if (d > hi) {
			continue;
		}
		sum_mid += mid - base;
		sum_off += s[i].phc - mid;
		sum_delay += d;
		used++;
	}
	/* can't happen (dmin <= hi), but be safe */
	if (used == 0) {
		return 0;
	}

	*sys_ns = base + sum_mid / used;
	*phc_ns = *sys_ns + sum_off / used;
	*delay_ns = sum_delay / used;
	if (dmin < up->mindelay) {
		up->mindelay = dmin;
	}
	return used;
}


/* Errors meaning "this method will never work on this device". */
static bool
method_unsupported(int err)
{
	return err == EOPNOTSUPP || err == ENOTTY || err == EINVAL
#if defined(ENOTSUP) && ENOTSUP != EOPNOTSUPP
	    || err == ENOTSUP
#endif
	    ;
}

/*
 * Pick the best method that works, starting at 'from'.  Returns
 * PHC_NMETHODS if nothing works at all.
 */
static enum phc_method
phc_probe(struct peer *peer, struct phcunit *up, enum phc_method from)
{
	struct refclockproc * const pp = peer->procptr;
	struct phc_sample s[MAX_SAMPLES];
	int m;

	for (m = from; m < PHC_NMETHODS; m++) {
		int r;

		if (m == PHC_PRECISE && (pp->sloppyclockflag & CLK_FLAG2)) {
			continue;
		}
		r = read_raw(up, (enum phc_method)m, s);
		if (r > 0) {
			return (enum phc_method)m;
		}
		DPRINT(1, ("%s: %s unavailable: %s\n", refclock_name(peer),
			   method_name[m], strerror(r < 0 ? -r : EIO)));
	}
	return PHC_NMETHODS;
}


/*
 * TAI-UTC offset in seconds in effect at 'when' (UTC), or -1 if unknown.
 *
 * Don't use sys_tai here: ntpd only updates it once synchronized, and
 * a TAI-mode PHC can't produce samples until it knows the offset.
 */
static int
phc_tai_offset(time_t when)
{
	int tai = leapsec_tai_offset(when);	/* from the leap second file */

	if (tai > 0) {
		return tai;
	}
	{
		struct timex tx;

		memset(&tx, 0, sizeof(tx));	/* modes = 0: read only */
		if (ntp_adjtime(&tx) >= 0 && tx.tai > 0) {
			return tx.tai;
		}
	}
	return -1;
}


/*
 * Open a PHC by device path, or by the name of a network interface
 * whose PHC we want.  On success the resolved device path is left in
 * 'dev'.
 */
static int
phc_open(struct peer *peer, const char *name, int flags,
	 char *dev, size_t devlen)
{
	if (name[0] != '/') {
		struct ethtool_ts_info info;
		struct ifreq ifr;
		int sock;

		memset(&ifr, 0, sizeof(ifr));
		memset(&info, 0, sizeof(info));
		if (strlen(name) >= sizeof(ifr.ifr_name)) {
			msyslog(LOG_ERR, "REFCLOCK: %s: bad interface name %s",
				refclock_name(peer), name);
			return -1;
		}
		strlcpy(ifr.ifr_name, name, sizeof(ifr.ifr_name));
		info.cmd = ETHTOOL_GET_TS_INFO;
		ifr.ifr_data = (char *)&info;

		sock = socket(AF_INET, SOCK_DGRAM | SOCK_CLOEXEC, 0);
		if (sock < 0 || ioctl(sock, SIOCETHTOOL, &ifr) < 0) {
			msyslog(LOG_ERR,
				"REFCLOCK: %s: can't query interface %s: %s",
				refclock_name(peer), name, strerror(errno));
			if (sock >= 0) {
				close(sock);
			}
			return -1;
		}
		close(sock);
		if (info.phc_index < 0) {
			msyslog(LOG_ERR, "REFCLOCK: %s: interface %s has no PHC",
				refclock_name(peer), name);
			return -1;
		}
		snprintf(dev, devlen, "/dev/ptp%d", info.phc_index);
	} else {
		strlcpy(dev, name, devlen);
	}
	return open(dev, flags | O_CLOEXEC);
}


/*
 * External PPS setup: route the pin to the channel and enable
 * timestamping of the chosen edge.
 */
static bool
extts_enable(struct peer *peer, struct phcunit *up, uint32_t mode,
	     bool enable)
{
	struct ptp_extts_request req;

#ifdef PTP_PIN_SETFUNC
	if (!(mode & MODE_NOPIN)) {
		struct ptp_pin_desc pin;

		memset(&pin, 0, sizeof(pin));
		pin.index = MODE_PIN(mode);
		pin.func = enable ? PTP_PF_EXTTS : PTP_PF_NONE;
		pin.chan = up->channel;
		if (ioctl(up->fd, PTP_PIN_SETFUNC, &pin) < 0) {
			if (enable) {
				msyslog(LOG_ERR,
					"REFCLOCK: %s: can't set pin %u to "
					"external timestamp channel %u: %s",
					refclock_name(peer), MODE_PIN(mode),
					up->channel, strerror(errno));
				return false;
			}
		}
	}
#endif

	memset(&req, 0, sizeof(req));
	req.index = up->channel;
	if (enable) {
		req.flags = PTP_ENABLE_FEATURE |
		    ((mode & MODE_FALLING) ? PTP_FALLING_EDGE
					   : PTP_RISING_EDGE);
	}
	if (ioctl(up->fd, PTP_EXTTS_REQUEST, &req) < 0) {
		if (enable) {
			msyslog(LOG_ERR,
				"REFCLOCK: %s: can't enable external "
				"timestamps on channel %u: %s",
				refclock_name(peer), up->channel,
				strerror(errno));
		}
		return false;
	}

#if defined(PTP_MASK_CLEAR_ALL) && defined(PTP_MASK_EN_SINGLE)
	/* Linux 6.7+: only deliver our channel's events to this fd */
	if (enable) {
		unsigned int ch = up->channel;

		if (ioctl(up->fd, PTP_MASK_CLEAR_ALL) < 0 ||
		    ioctl(up->fd, PTP_MASK_EN_SINGLE, &ch) < 0) {
			DPRINT(1, ("%s: event mask not set: %s\n",
				   refclock_name(peer), strerror(errno)));
		}
	}
#endif
	return true;
}


/*
 * phc_start - open the PHC and pick a measurement method
 */
static bool
phc_start(
	int unit,
	struct peer *peer
	)
{
	struct refclockproc * const pp = peer->procptr;
	const uint32_t mode = peer->cfg.mode;
	struct ptp_clock_caps caps;
	struct phcunit *up;
	char name[32], dev[PATH_MAX] = "";
	const char *path;
	int fd;

	pp->clockname = NAME;	/* early, for refclock_name() in errors */
	pp->clockdesc = DESCRIPTION;

	if (peer->cfg.path) {
		path = peer->cfg.path;
	} else {
		snprintf(name, sizeof(name), DEVICE, unit);
		path = name;
	}

	fd = phc_open(peer, path, (mode & MODE_EXTPPS) ? O_RDWR : O_RDONLY,
		      dev, sizeof(dev));
	if (fd < 0) {
		if (dev[0] != '\0' || path[0] == '/') {
			msyslog(LOG_ERR, "REFCLOCK: %s: open %s failed: %s",
				refclock_name(peer), path, strerror(errno));
		}
		return false;
	}

	memset(&caps, 0, sizeof(caps));
	if (ioctl(fd, PTP_CLOCK_GETCAPS, &caps) < 0) {
		msyslog(LOG_ERR,
			"REFCLOCK: %s: %s is not a PTP hardware clock: %s",
			refclock_name(peer), dev, strerror(errno));
		close(fd);
		return false;
	}

	up = emalloc_zero(sizeof(*up));
	up->fd = fd;
	up->clkid = FD_TO_CLOCKID(fd);
	up->nsamples = DEF_SAMPLES;
	up->mindelay = INT64_MAX;

	pp->unitptr = up;
	pp->io.clock_recv = NULL;
	pp->io.srcclock = peer;
	pp->io.datalen = 0;
	pp->io.fd = -1;

	memcpy(&pp->refid, REFID, REFIDLEN);
	peer->precision = PRECISION;
	peer->sstclktype = CTL_SST_TS_UHF;

	if (mode & MODE_EXTPPS) {
		up->extpps = true;
		up->channel = MODE_CHANNEL(mode);
		if ((int)up->channel >= caps.n_ext_ts) {
			msyslog(LOG_ERR,
				"REFCLOCK: %s: %s has %d external timestamp "
				"channel(s), channel %u requested",
				refclock_name(peer), dev, caps.n_ext_ts,
				up->channel);
			goto fail;
		}
		if (!extts_enable(peer, up, mode, true)) {
			goto fail;
		}
		memcpy(&pp->refid, REFID_PPS, REFIDLEN);
		peer->sstclktype = CTL_SST_TS_ATOM;
	}

	/*
	 * Fudge flags aren't known yet, so probe from the top here and
	 * re-probe in phc_control() once they are.
	 */
	up->method = phc_probe(peer, up, PHC_PRECISE);
	if (up->method == PHC_NMETHODS) {
		msyslog(LOG_ERR, "REFCLOCK: %s: cannot read %s",
			refclock_name(peer), dev);
		goto fail;
	}
	msyslog(LOG_INFO, "REFCLOCK: %s: using %s via %s%s",
		refclock_name(peer), dev, method_name[up->method],
		up->extpps ? ", external PPS" : "");
	return true;

    fail:
	phc_shutdown(pp);
	return false;
}


/*
 * phc_control - apply fudge settings
 */
static void
phc_control(
	int unit,
	const struct refclockstat *in_st,
	struct refclockstat *out_st,
	struct peer *peer
	)
{
	struct refclockproc * const pp = peer->procptr;
	struct phcunit * const up = pp->unitptr;
	unsigned int ns;
	enum phc_method m;

	UNUSED_ARG(unit);
	UNUSED_ARG(in_st);
	UNUSED_ARG(out_st);

	if (up == NULL) {
		return;
	}

	ns = MODE_SAMPLES(peer->cfg.mode);
	if (ns == 0) {
		up->nsamples = DEF_SAMPLES;
	} else if (ns <= MAX_SAMPLES) {
		up->nsamples = ns;
	} else {
		msyslog(LOG_WARNING,
			"REFCLOCK: %s: %u samples out of range 1..%d, using %d",
			refclock_name(peer), ns, MAX_SAMPLES, DEF_SAMPLES);
		up->nsamples = DEF_SAMPLES;
	}

	/* flag2 may have changed whether PRECISE is allowed */
	m = phc_probe(peer, up, PHC_PRECISE);
	if (m != PHC_NMETHODS && m != up->method) {
		up->method = m;
		msyslog(LOG_INFO, "REFCLOCK: %s: now using %s",
			refclock_name(peer), method_name[m]);
	}
}


/*
 * phc_shutdown - disable external timestamps and close the device
 */
static void
phc_shutdown(
	struct refclockproc *pp
	)
{
	struct phcunit * const up = pp->unitptr;

	if (up == NULL) {
		return;
	}
	if (up->extpps && up->fd >= 0) {
		struct ptp_extts_request req;

		memset(&req, 0, sizeof(req));	/* flags 0: disable */
		req.index = up->channel;
		(void)ioctl(up->fd, PTP_EXTTS_REQUEST, &req);
	}
	if (up->fd >= 0) {
		close(up->fd);
	}
	free(up);
	pp->unitptr = NULL;
}


/*
 * Take a reading, falling back to a lesser method if the current one
 * has stopped being supported.  Returns samples combined, 0 on failure.
 */
static int
phc_measure(struct peer *peer, struct phcunit *up,
	    int64_t *phc_ns, int64_t *sys_ns, int64_t *delay_ns)
{
	struct phc_sample s[MAX_SAMPLES];
	int r;

	r = read_raw(up, up->method, s);
	if (r < 0 && method_unsupported(-r)) {
		/* e.g. driver reloaded without cross-timestamp support */
		enum phc_method m = phc_probe(peer, up, up->method + 1);

		if (m != PHC_NMETHODS) {
			msyslog(LOG_NOTICE,
				"REFCLOCK: %s: %s failed (%s), falling back to %s",
				refclock_name(peer), method_name[up->method],
				strerror(-r), method_name[m]);
			up->method = m;
			r = read_raw(up, m, s);
		}
	}
	if (r <= 0) {
		DPRINT(1, ("%s: read failed: %s\n", refclock_name(peer),
			   strerror(r < 0 ? -r : EIO)));
		return 0;
	}
	r = combine(up, s, r, phc_ns, sys_ns, delay_ns);
	if (r == 0) {
		DPRINT(1, ("%s: burst rejected\n", refclock_name(peer)));
	}
	return r;
}


/*
 * phc_timer - take one reading, once per second
 */
static void
phc_timer(
	int unit,
	struct peer *peer
	)
{
	struct refclockproc * const pp = peer->procptr;
	struct phcunit * const up = pp->unitptr;
	int64_t phc_ns = 0, sys_ns = 0, delay_ns = 0;
	struct timespec phc_ts, sys_ts;
	int used, c;

	UNUSED_ARG(unit);

	if (up == NULL) {
		return;
	}
	up->ticks++;

	used = phc_measure(peer, up, &phc_ns, &sys_ns, &delay_ns);
	if (used == 0) {
		up->bad++;
		if (up->extpps) {
			phc_drain_extts(peer, up);  /* don't let events pile up */
		}
		return;
	}
	up->good++;
	up->used += used;

	if (up->extpps) {
		/* just remember the mapping for converting pulses */
		up->m_sys[0] = up->m_sys[1];
		up->m_off[0] = up->m_off[1];
		up->m_sys[1] = sys_ns;
		up->m_off[1] = phc_ns - sys_ns;
		if (up->m_n < 2) {
			up->m_n++;
		}
		phc_drain_extts(peer, up);
		return;
	}

	/* PHC on TAI?  Bring it to UTC. */
	if (pp->sloppyclockflag & CLK_FLAG1) {
		/*
		 * Around a leap the sample may be off by a second for a
		 * moment; the median filter and clock select cope.
		 */
		int tai = phc_tai_offset((time_t)(sys_ns / NS_PER_SEC));

		if (tai < 0) {
			if (!up->tai_warned) {
				msyslog(LOG_WARNING,
					"REFCLOCK: %s: flag1 (TAI) set but "
					"TAI-UTC offset unknown; configure "
					"a leapfile", refclock_name(peer));
				up->tai_warned = true;
			}
			up->good--;
			up->bad++;
			return;
		}
		phc_ns -= (int64_t)tai * NS_PER_SEC;
	}

	phc_ts = ns_to_ts(phc_ns);
	sys_ts = ns_to_ts(sys_ns);

	/* timecode as seen by "ntpq -c cv" */
	c = snprintf(pp->a_lastcode, sizeof(pp->a_lastcode), "%lld.%09ld",
		     (long long)phc_ts.tv_sec, (long)phc_ts.tv_nsec);
	pp->lencode = (c > 0 && c < (int)sizeof(pp->a_lastcode)) ?
	    (unsigned)c : 0;

	/* half the (averaged) bracket bounds the error */
	peer->precision = ns_to_precision(delay_ns > 0 ? delay_ns / 2 : 1);
	pp->leap = LEAP_NOWARNING;

	refclock_process_offset(pp, tspec_stamp_to_lfp(phc_ts),
				tspec_stamp_to_lfp(sys_ts), pp->fudgetime1);
}


/*
 * Map a PHC timestamp to system time using the last two readings,
 * interpolating (or extrapolating) the offset linearly.  Returns false
 * if the readings are too old to trust.
 */
static bool
phc_to_sys(const struct phcunit *up, int64_t phc, int64_t *sys)
{
	int64_t t, off;

	if (up->m_n < 1) {
		return false;
	}
	t = phc - up->m_off[1];		/* first guess at system time */
	if (t - up->m_sys[1] > MODEL_MAX_AGE ||
	    up->m_sys[1] - t > MODEL_MAX_AGE) {
		return false;
	}
	off = up->m_off[1];
	if (up->m_n == 2 && up->m_sys[1] > up->m_sys[0]) {
		double slope = (double)(up->m_off[1] - up->m_off[0]) /
		    (double)(up->m_sys[1] - up->m_sys[0]);

		off += (int64_t)llround(slope * (double)(t - up->m_sys[1]));
	}
	*sys = phc - off;
	return true;
}

/*
 * Turn one external timestamp into a PPS sample.
 */
static void
phc_pulse(struct peer *peer, struct phcunit *up,
	  const struct ptp_extts_event *ev)
{
	struct refclockproc * const pp = peer->procptr;
	int64_t pulse = pct_to_ns(&ev->t);
	int64_t sys, sec;
	struct timespec ref_ts, sys_ts;
	int c;

	if (ev->index != up->channel) {
		return;		/* another channel (pre-6.7 kernels) */
	}
	/*
	 * Some hardware timestamps both edges whatever we ask for; the
	 * second edge arrives within the pulse width.
	 */
	if (up->last_pulse != 0 &&
	    pulse - up->last_pulse < MIN_PULSE_GAP &&
	    pulse - up->last_pulse > -MIN_PULSE_GAP) {
		DPRINT(2, ("%s: ignoring edge %lld ns after last\n",
			   refclock_name(peer),
			   (long long)(pulse - up->last_pulse)));
		return;
	}
	up->last_pulse = pulse;

	if (!phc_to_sys(up, pulse, &sys)) {
		DPRINT(1, ("%s: no fresh PHC reading for pulse\n",
			   refclock_name(peer)));
		return;
	}

	/* the pulse marks the nearest whole second */
	sec = (sys + NS_PER_SEC / 2) / NS_PER_SEC;
	ref_ts.tv_sec = (time_t)sec;
	ref_ts.tv_nsec = 0;
	sys_ts = ns_to_ts(sys);

	c = snprintf(pp->a_lastcode, sizeof(pp->a_lastcode), "%lld.%09ld",
		     (long long)sys_ts.tv_sec, (long)sys_ts.tv_nsec);
	pp->lencode = (c > 0 && c < (int)sizeof(pp->a_lastcode)) ?
	    (unsigned)c : 0;

	pp->leap = LEAP_NOWARNING;
	refclock_process_offset(pp, tspec_stamp_to_lfp(ref_ts),
				tspec_stamp_to_lfp(sys_ts), pp->fudgetime1);
	peer->cfg.flags |= FLAG_PPS;
	up->pulses++;
}

/*
 * Read whatever external timestamp events are queued, never blocking.
 */
static void
phc_drain_extts(struct peer *peer, struct phcunit *up)
{
	struct ptp_extts_event ev[EXTTS_BATCH];
	int reads;

	for (reads = 0; reads < EXTTS_MAX_READS; reads++) {
		struct pollfd pfd;
		ssize_t r;
		size_t i;

		pfd.fd = up->fd;
		pfd.events = POLLIN;
		pfd.revents = 0;
		if (poll(&pfd, 1, 0) != 1 || !(pfd.revents & POLLIN)) {
			return;
		}
		r = read(up->fd, ev, sizeof(ev));
		if (r <= 0) {
			if (r < 0 && errno != EINTR && errno != EAGAIN) {
				msyslog(LOG_ERR,
					"REFCLOCK: %s: event read: %s",
					refclock_name(peer), strerror(errno));
			}
			return;
		}
		for (i = 0; i < (size_t)r / sizeof(ev[0]); i++) {
			phc_pulse(peer, up, &ev[i]);
		}
	}
}


/*
 * phc_poll - hand accumulated samples to the clock filter
 */
static void
phc_poll(
	int unit,
	struct peer *peer
	)
{
	struct refclockproc * const pp = peer->procptr;
	struct phcunit * const up = pp->unitptr;

	UNUSED_ARG(unit);

	pp->polls++;
	if (up == NULL) {
		refclock_report(peer, CEVNT_FAULT);
		return;
	}

	if (pp->sloppyclockflag & CLK_FLAG4) {
		mprintf_clock_stats(peer, "%d %d %d %.1f %lld %d %s%s",
				    up->ticks, up->good, up->bad,
				    up->good ? (double)up->used / up->good : 0.0,
				    (long long)(up->mindelay == INT64_MAX ?
						-1 : up->mindelay),
				    up->pulses, method_name[up->method],
				    up->extpps ? "+extpps" : "");
	}
	up->ticks = up->good = up->bad = up->used = up->pulses = 0;
	up->mindelay = INT64_MAX;

	/*
	 * A PPS only gives the fraction of a second; don't use it until
	 * some other source has numbered the seconds.
	 */
	if (up->extpps && sys_vars.sys_leap == LEAP_NOTINSYNC) {
		pp->codeproc = pp->coderecv;
		peer->cfg.flags &= ~FLAG_PPS;
		refclock_report(peer, CEVNT_TIMEOUT);
		return;
	}

	if (pp->coderecv != pp->codeproc) {
		pp->lastref = pp->lastrec;
		refclock_receive(peer);
	} else {
		if (up->extpps) {
			peer->cfg.flags &= ~FLAG_PPS;
		}
		refclock_report(peer, CEVNT_TIMEOUT);
	}
}
