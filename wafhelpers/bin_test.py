"""Run a suite of tests on the listed binaries."""
from __future__ import print_function
import ntp.util
import os
import os.path
import sys
import waflib.Context
import waflib.Logs
import waflib.Utils
sys.path.insert(0, "%s/main/tests/pylib" % waflib.Context.out_dir)

verStr = ntp.util.stdversion()

cmd_map = {
    ("main/ntpclients/ntpleapfetch", "--version"): "ntpleapfetch %s\n"
                                                   % verStr,
    ("main/ntpd/ntpd", "--version"): "ntpd %s\n" % verStr,
    ("main/ntpfrob/ntpfrob", "-V"): "ntpfrob %s\n" % verStr,
    ("main/ntptime/ntptime", "-V"): "ntptime %s\n" % verStr
}
cmd_map_python = {
    ("main/ntpclients/ntpdig", "--version"): "ntpdig %s\n" % verStr,
    ("main/ntpclients/ntpkeygen", "--version"): "ntpkeygen %s\n" % verStr,
    ("main/ntpclients/ntpq", "--version"): "ntpq %s\n" % verStr,
    ("main/ntpclients/ntpsnmpd", "--version"): "ntpsnmpd %s\n" % verStr,
    ("main/ntpclients/ntpsweep", "--version"): "ntpsweep %s\n" % verStr,
    ("main/ntpclients/ntptrace", "--version"): "ntptrace %s\n" % verStr,
    ("main/ntpclients/ntpwait", "--version"): "ntpwait %s\n" % verStr
}
# Need argparse
cmd_map_python_argparse = {
    ("main/ntpclients/ntplogtemp", "--version"): "ntplogtemp %s\n" % verStr,
    ("main/ntpclients/ntpviz", "--version"): "ntpviz %s\n" % verStr,
}
# Need python curses
cmd_map_python_curses = {
    ("main/ntpclients/ntpmon", "--version"): "ntpmon %s\n" % verStr,
}

test_logs = []


def addLog(color, text):
    test_logs.append((color, text))


def bin_test_summary(ctx):
    for i in test_logs:
        waflib.Logs.pprint(i[0], i[1])


def run(cmd, reg, pythonic):
    """Run an individual non-python test."""
    check = False

    prefix = "running: " + " ".join(cmd)

    if not os.path.exists("%s/%s" % (waflib.Context.out_dir, cmd[0])):
        addLog("YELLOW", prefix + " SKIPPING (does not exist)")
        return False

    if pythonic:
        cmd = [sys.executable] + list(cmd)
    p = waflib.Utils.subprocess.Popen(cmd, env={'PYTHONPATH': '%s/main/tests/pylib' %
                                                waflib.Context.out_dir},
                                      universal_newlines=True,
                                      stdin=waflib.Utils.subprocess.PIPE,
                                      stdout=waflib.Utils.subprocess.PIPE,
                                      stderr=waflib.Utils.subprocess.PIPE, cwd=waflib.Context.out_dir)

    stdout, stderr = p.communicate()

    if (stdout == reg) or (stderr == reg):
        check = True

    if check:
        addLog("GREEN", prefix + "  OK")
        return True
    addLog("RED", prefix + "  FAILED")
    addLog("PINK", "Expected: " + reg)
    if stdout:
        addLog("PINK", "Got (stdout): " + stdout)
    if stderr:
        addLog("PINK", "Got (stderr): " + stderr)
    return False


def cmd_bin_test(ctx, config):
    """Run a suite of binary tests."""
    fails = 0

    if ctx.env['PYTHON_ARGPARSE']:
        cmd_map_python.update(cmd_map_python_argparse)

    if ctx.env['PYTHON_CURSES']:
        cmd_map_python.update(cmd_map_python_curses)

    for cmd in sorted(cmd_map):
        if not run(cmd, cmd_map[cmd], False):
            fails += 1

    for cmd in sorted(cmd_map_python):
        if not run(cmd, cmd_map_python[cmd], True):
            fails += 1

    if 1 == fails:
        bin_test_summary(ctx)
        ctx.fatal("1 binary test failed!")
    elif 1 < fails:
        bin_test_summary(ctx)
        ctx.fatal("%d binary tests failed!" % fails)
