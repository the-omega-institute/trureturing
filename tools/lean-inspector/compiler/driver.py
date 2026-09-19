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
ORIGIN_ARG = '-Dweak.compilerOrigin=true'


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
        extra = [] if '-c' in args or '-shared' in args else [str(root / path) for path in config['objects']]
        os.execve(config['leanc'], [config['leanc'], *extra, *args],
            dict(os.environ, LEAN_SYSROOT=config['base']))
    if args in (['--print-prefix'], ['--print-libdir']):
        print(root if args == ['--print-prefix'] else root / 'lib/lean')
        return
    if args in (['--version'], ['--short-version'], ['--githash'], ['--features'], ['--help']):
        os.execv(config['lean'], [config['lean'], *args])
    # Lake owns package selection and hashes moreLeanArgs plus the package's
    # compilerInput dependency. Unmarked Lake modules use the actual stock
    # frontend and stock builtin imports, including on a cache miss. A stock
    # cached theorem never acquires a producer record from this dispatch.
    origin = ORIGIN_ARG in args
    setup = any(arg in ('--setup', '-u') or arg.startswith('--setup=') for arg in args)
    if setup and not origin:
        env = dict(os.environ, LEAN_SYSROOT=config['base'])
        for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'PATH'):
            if key in env:
                env[key] = os.pathsep.join(
                    config['base'] + path[len(str(root)):]
                    if path == str(root) or path.startswith(str(root) + os.sep) else path
                    for path in env[key].split(os.pathsep))
        env.pop('LEAN_COMPILER_ORIGIN', None)
        os.execve(config['lean'], [config['lean'], *args], env)
    if origin:
        if os.environ.get('LEAN_COMPILER_ORIGIN') != config['origin']:
            raise SystemExit('project compiler: compiler origin environment mismatch')
        args = [arg for arg in args if arg != ORIGIN_ARG]
    try:
        translated = translate(args)
    except getopt.GetoptError as error:
        raise SystemExit('project compiler: unsupported argument: ' + str(error)) from error
    os.execv(str(root / 'bin/frontend'), [str(root / 'bin/frontend'), *translated])


if __name__ == '__main__':
    main()
