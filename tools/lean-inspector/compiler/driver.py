#!/usr/bin/env python3
"""Launch the project compiler's pinned Lean Shell frontend. No origin inference."""
import getopt
import json
import os
from pathlib import Path
import sys

# Supported frontend flags are delegated to Lean.ShellOptions.process, then
# Lean.shellMain. Thread-manager/server/incremental-snapshot flags fail closed;
# this executable is a batch compiler, not a replacement language server.
LONG = {
    'run': ('r', False), 'o': ('o', True), 'i': ('i', True),
    'stdin': ('I', False), 'root': ('R', True), 'memory': ('M', True),
    'trust': ('t', True), 'stats': ('a', False), 'quiet': ('q', False),
    'deps': ('d', False), 'src-deps': ('O', False), 'deps-json': ('N', False),
    'timeout': ('T', True), 'c': ('c', True), 'bc': ('b', True),
    'plugin': ('p', True), 'load-dynlib': ('l', True), 'setup': ('u', True),
    'error': ('E', True), 'json': ('J', False),
}
SHORT = 'D:o:i:b:c:qt:R:M:T:ap:l:u:E:dIONJr'


def translate(args):
    # Like the stock CLI, --run ends option processing; program arguments are
    # never parsed as compiler switches.
    stop = next((i for i, arg in enumerate(args) if arg in ('--run', '-r')), None)
    tail = [] if stop is None else args[stop + 1:]
    opts, files = getopt.gnu_getopt(args if stop is None else args[:stop], SHORT,
        [name + ('=' if takes else '') for name, (_, takes) in LONG.items()])
    out = []
    for flag, value in opts:
        code = LONG[flag[2:]][0] if flag.startswith('--') else flag[1:]
        out.extend([code, value])
    if stop is not None:
        out.extend(['r', ''])
        files += tail
    return out + ['--'] + files


def main():
    root = Path(__file__).resolve().parents[1]
    config = json.loads((root / 'driver.json').read_text())
    args = sys.argv[1:]
    if Path(sys.argv[0]).name == 'leanc':
        # Object compilation/shared plugins do not embed the compiler. Native
        # executables link the same generator objects before the pinned archive.
        extra = [] if '-c' in args or '-shared' in args else config['objects']
        os.execve(config['leanc'], [config['leanc'], *extra, *args],
            dict(os.environ, LEAN_SYSROOT=config['base']))
    if args in (['--print-prefix'], ['--print-libdir']):
        print(root if args == ['--print-prefix'] else root / 'lib/lean')
        return
    if args in (['--version'], ['--short-version'], ['--githash'], ['--features'], ['--help']):
        os.execv(config['lean'], [config['lean'], *args])
    try:
        translated = translate(args)
    except getopt.GetoptError as error:
        raise SystemExit('project compiler: unsupported argument: ' + str(error)) from error
    os.execv(str(root / 'bin/frontend'), [str(root / 'bin/frontend'), *translated])


if __name__ == '__main__':
    main()
