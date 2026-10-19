#!/usr/bin/env python3
"""Validated Stage A continuation inputs shared by the two generators."""
import re
from pathlib import Path
from common import entry, fail, load, name, read

MODULE = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+"


def targets(values):
    parts = ' '.join(values).split()
    if not parts or any(not re.fullmatch(MODULE, part) for part in parts):
        fail(13, 'NO_TARGETS: dotted Lean module names required')
    return ' '.join(parts)


def inputs(lane, suffix, envelope, tree, previous):
    name(lane); name(suffix)
    if not Path(tree).is_dir(): fail(11, 'worktree missing: ' + tree)
    data = load(envelope)
    if not isinstance(data, dict) or not isinstance(data.get('conclusion'), dict):
        fail(13, 'envelope conclusion must be an object')
    return data['conclusion'], read(previous)


def precondition(tree, previous):
    if Path(previous).name.startswith('rework-'):
        return (f'Work on the current head of `{tree}`; do not fast-forward, merge or rebase '
                f'`origin/dev` in this step. Commit fixes on top of that head.')
    return (f'Preserve the uncommitted Stage A delivery in `{tree}`. Run `git fetch origin dev && '
            f'git merge --ff-only origin/dev`; stash and pop around the merge if needed.')


def strings(value):
    if isinstance(value, str): yield value
    elif isinstance(value, dict):
        for child in value.values(): yield from strings(child)
    elif isinstance(value, list):
        for child in value: yield from strings(child)


def envelope_targets(conclusion):
    # Capture whole tokens within command and Markdown boundaries, then validate.
    token = r'[^\s";&|)`]+'
    for text in strings(conclusion):
        match = re.search(r'\bLEAN_TARGETS=(?:"([^"]*)"|\x27([^\x27]*)\x27|(' + token +
                          r'(?:[^\S\r\n]+' + token + r')*))', text)
        if match:
            return targets([next(x for x in match.groups() if x is not None)])
    fail(13, 'NO_TARGETS_IN_ENVELOPE')


if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--selftest']:
        from continuation_selftest import run
        sys.exit(run('mirrorfix_cont') or run('lockretry_head'))
    sys.exit(entry(lambda args: fail(10, 'source-only continuation helpers')))
