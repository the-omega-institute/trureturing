#!/usr/bin/env python3
"""Portable inputs and error codes shared by brief generators."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
REPO = TOOLS.parents[3]


class BriefError(Exception):
    def __init__(self, code, message):
        self.code, self.message = code, message


def fail(code, message):
    raise BriefError(code, message)


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
        self.state = Path(os.environ.get('OP_STATE', Path.home() / '.local/state/trureturing-op')).resolve()
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
        if not re.fullmatch('[0-9a-f]{24}', flight):
            fail(13, 'invalid flight id')
        results = []
        for path in (self.sshx / flight).glob('attempt-*/result.json'):
            match = re.fullmatch(r'attempt-(\d+)', path.parent.name)
            if match and path.is_file():
                results.append((int(match[1]), path))
        if not results:
            fail(11, 'missing result: ' + flight)
        return max(results)[1]


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
        print('BRIEF_INVALID_INPUT ' + str(exc), file=sys.stderr)
        return 13
    except (OSError, subprocess.SubprocessError) as exc:
        print('BRIEF_IO_ERROR ' + str(exc), file=sys.stderr)
        return 16


if __name__ == '__main__':
    sys.exit(entry(lambda args: fail(10, 'source-only module')))
