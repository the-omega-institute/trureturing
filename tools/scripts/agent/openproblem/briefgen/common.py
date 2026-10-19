#!/usr/bin/env python3
"""Portable inputs and error codes shared by brief generators."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import traceback

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
REPO = TOOLS.parents[3]
MAIN_WARM_STAMP = '.lake/build/.main-built-at'

BUILD_SCOPE = '**Build scope (binding; supersedes every other build instruction in this brief).** Every `make lean` below means `make lean LEAN_TARGETS="<the dotted names of the delivered modules and of every frozen module you re-pin>"`, and every `make lean-report` means `make lean-report-scoped LEAN_TARGETS="<the same list>"`. Never run `make lean`, `make lean-report`, `make test` or `make gate` without a target list. The Lean build lock is shared by every worktree on this machine: an untargeted build after a merge of `origin/dev` recompiles hundreds of unrelated modules for hours and blocks every other lane. The doors (`make deposit-uncovered`, `make deposit`, `make cover`, `make emit`) choose their own scope (CLAUDE.md §8.2). If a step cannot be done with a target list, skip it and name it under `not_run`.'


class BriefError(Exception):
    def __init__(self, code, message):
        self.code, self.message = code, message


def fail(code, message):
    raise BriefError(code, message)


def uint(value, label='value'):
    if not re.fullmatch(r'[1-9][0-9]*', str(value)):
        fail(13, label + ' must be a positive integer')
    return int(value)


def sha(value):
    if not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{40}', value):
        fail(13, 'full commit SHA required')
    return value


def state_dir():
    base = Path(os.environ.get('XDG_STATE_HOME') or Path.home() / '.local/state')
    return Path(os.environ.get('OP_STATE') or base / 'trureturing-op').resolve()


def main_lean_lock():
    return Path(os.environ.get('OP_REFRESH_LOCK') or state_dir() / 'main-lean.lock').resolve()


def main_warm_stamp(main):
    return Path(main) / MAIN_WARM_STAMP


def name(value):
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', value):
        fail(13, 'invalid name: ' + value)
    return value


def read(path):
    path = Path(path)
    if not path.is_file():
        fail(11, 'missing input: ' + str(path))
    return path.read_text()


def load(path):
    return json.loads(read(path))


def lane_spec(path):
    data = load(path)
    for key in ('lane', 'title', 'worktree', 'branch', 'module', 'gid', 'target_md', 'commit_subject'):
        if not isinstance(data.get(key), str) or not data[key]:
            fail(13, 'lane field required: ' + key)
    name(data['lane'])
    if not re.fullmatch(r'D5(?:/[A-Za-z_][A-Za-z0-9_]*)+', data['module']):
        fail(13, 'one extension-free D5 module path required')
    if not data['gid'].startswith(data['module'] + '.'):
        fail(13, 'GID must belong to the settling module')
    return data


class Context:
    def __init__(self, scratch=None, required=()):
        if sys.version_info < (3, 9):
            fail(12, 'Python 3.9 or newer required')
        for tool in ('git', 'python3', *required):
            if not shutil.which(tool):
                fail(12, 'missing tool: ' + tool)
        value = scratch or os.environ.get('OP_SCRATCH')
        if not value:
            fail(11, 'OP_SCRATCH required')
        self.scratch = Path(value).resolve()
        if not self.scratch.is_dir():
            fail(11, 'scratch directory missing: ' + str(self.scratch))
        self.state = state_dir()
        self.sshx = Path(os.environ.get('SSHX_HOME', Path.home() / '.sshx')).resolve()
        self.prefix = os.environ.get('OP_NAME_PREFIX', '')
        if self.prefix:
            name(self.prefix)
        listing = subprocess.check_output(['git', '-C', str(REPO), 'worktree', 'list', '--porcelain'], text=True)
        self.main = Path(listing.splitlines()[0].removeprefix('worktree '))
        remote = subprocess.check_output(['git', '-C', str(REPO), 'remote', 'get-url', 'origin'], text=True).strip()
        self.slug = re.sub(r'\.git$', '', re.sub(r'^.*(?:github\.com[:/])', '', remote))
        self.provenance = os.environ.get('OP_PROVENANCE_MD', '')
        self.session = os.environ.get('OP_ORCHESTRATOR_SESSION', '')

    def block(self, filename):
        name(filename)
        override = self.scratch / 'briefs' / filename
        path = override if override.is_file() else TOOLS / 'templates/blocks' / filename
        read(path)
        return path

    def result(self, flight):
        result = subprocess.run(
            ['/bin/bash', '-c', '. "$1"; op_latest_result "$2"',
             'brief-result', str(TOOLS / 'pipeline/common.sh'), flight],
            env=dict(os.environ, SSHX_HOME=str(self.sshx)),
            capture_output=True, text=True)
        if result.returncode:
            message = result.stderr.strip()
            if 'PIPELINE_DATA_ERROR invalid flight id' in message.splitlines():
                fail(13, 'invalid flight id')
            fail(16, message or 'result lookup failed')
        path = result.stdout.strip()
        if path == 'NO_RESULT':
            fail(11, 'missing result: ' + flight)
        return Path(path)


def entry(main, argv=None, minimum=0, maximum=None, tool=None):
    args = list(sys.argv if argv is None else argv)
    try:
        if args[1:] == ['--selftest']:
            from selftest import run
            return run(Path(tool or args[0]).resolve())
        if len(args) - 1 < minimum or (maximum is not None and len(args) - 1 > maximum) or any(a.startswith('--invalid') for a in args[1:]):
            fail(10, 'invalid arguments; see module usage')
        return main(args) or 0
    except BriefError as exc:
        print('BRIEF_ERROR ' + exc.message, file=sys.stderr)
        return exc.code
    except FileNotFoundError as exc:
        print('BRIEF_INPUT_MISSING ' + str(exc), file=sys.stderr)
        return 11
    except (AssertionError, ValueError, KeyError, IndexError, TypeError, AttributeError) as exc:
        detail = str(exc).strip()
        if not detail:
            frame = traceback.extract_tb(exc.__traceback__)[-1]
            detail = f'{Path(frame.filename).name}:{frame.lineno} in {frame.name}: {frame.line or "no exception message"}'
        print(f'BRIEF_INVALID_INPUT {type(exc).__name__}: {detail}', file=sys.stderr)
        return 13
    except (OSError, subprocess.SubprocessError) as exc:
        print('BRIEF_IO_ERROR ' + str(exc), file=sys.stderr)
        return 16


def settings(argv):
    readers = {'state-dir': state_dir, 'main-lean-lock': main_lean_lock}
    if len(argv) != 2 or argv[1] not in readers:
        fail(10, 'common.py state-dir|main-lean-lock')
    print(readers[argv[1]]())


if __name__ == '__main__':
    sys.exit(entry(settings))
