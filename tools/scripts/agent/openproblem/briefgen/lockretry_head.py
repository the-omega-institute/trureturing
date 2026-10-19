#!/usr/bin/env python3
"""Usage: lockretry_head.py LANE SUFFIX ENVELOPE WORKTREE PREV_BRIEF OUT"""
from pathlib import Path
import sys
from common import Context, entry
from continuation import envelope_targets, inputs, precondition


def main(argv):
    Context()
    lane, suffix, env, tree, previous, out = argv[1:]
    conclusion, rest = inputs(lane, suffix, env, tree, previous)
    targets = envelope_targets(conclusion)
    head = f'''# Stage A continuation {suffix} — lane `op-{lane}` (binding; overrides earlier heads)

Read `{env}` for the completed checks and pending targeted build. Keep its verified readings; do not infer that another build or runner has stopped.

1. **Preconditions.** {precondition(tree, previous)} Report the hash of every delivered file before and after.
2. **Build.** Run `make lean LEAN_TARGETS="{targets}"` and wait for completion. The shared Lean build lock queue is expected; the time box is four hours from the first command. Never run an untargeted `make lean`, `make lean-report`, `make test` or `make gate`. Every direct Lean invocation must use the shared build lock. Do not stop any build, runner or dispatch process.
3. **After success.** Run `make emit` twice (the second reports 0 changed blueprints), the header check on every delivered module and `#print axioms` on every public declaration (three standard axioms).
4. **Lean errors.** Fix only the reported error within the Stage A rules below and report the change.
5. **Return.** Keep the previous envelope fields, update their readings and return `verdict: mirror-ready` when steps 2–3 pass; otherwise `open` with exact readings. Stop before any freeze door.

'''
    Path(out).write_text(head + rest)
    print('HEAD_OK', lane, suffix, targets)


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        from continuation_selftest import run
        sys.exit(run('lockretry_head'))
    sys.exit(entry(main, minimum=6, maximum=6))
