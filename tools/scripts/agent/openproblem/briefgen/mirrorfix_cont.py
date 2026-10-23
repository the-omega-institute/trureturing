#!/usr/bin/env python3
"""Usage: mirrorfix_cont.py LANE SUFFIX ENV WORKTREE PREV PREV_MIRROR OUT OUT_MIRROR ROUND TARGETS..."""
import json
from pathlib import Path
import re
import sys
from common import Context, entry, fail, read
from continuation import inputs, precondition, targets


def main(argv):
    Context()
    lane, suffix, env, tree, previous, mirror, out, out_mirror, rnd = argv[1:10]
    conclusion, rest = inputs(lane, suffix, env, tree, previous)
    mirror_rest = read(mirror)
    build_targets = targets(argv[10:])
    if not re.fullmatch(r'[1-9][0-9]*', rnd): fail(13, 'positive round required')
    if Path(out).resolve() == Path(out_mirror).resolve(): fail(13, 'distinct output paths required')
    findings = conclusion.get('blocking_findings')
    if conclusion.get('verdict') != 'reject' or not isinstance(findings, list) or not findings:
        fail(13, 'NO_BLOCKING_FINDINGS: rejected mirror required')
    items = []
    for finding in findings:
        if not isinstance(finding, dict) or any(not finding.get(k) for k in ('file_line', 'claim', 'fix')):
            fail(13, 'finding requires file_line, claim and fix')
        def text(key):
            value = finding.get(key, '')
            return (value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)).replace('\n', ' ')
        items.append(f'   - `{text("file_line")}`: {text("claim")}. Owner: `{text("owner")}`. Fix: {text("fix")}')
    pre = precondition(tree, previous)
    head = f'''# Stage A continuation {suffix} — lane `op-{lane}` (binding; overrides earlier heads)

Read the rejected pre-freeze mirror `{env}` and apply all {len(findings)} blocking findings. Preserve the fixes already in the tree.

1. **Preconditions.** {pre} Report the hash of every delivered file before and after.
2. **Fixes.** Keep each declaration's visibility, label and consumers. If a route does not compile, report its exact error and keep the current proof.
{chr(10).join(items)}
3. **Neighbour sweep.** Check every other closed local `have` and private helper of the same shape against the named owners and siblings by compiled application; report one row per item.
4. **Build.** Run `make lean LEAN_TARGETS="{build_targets}"`, then `make emit` twice (the second reports 0 changed), the header check and `#print axioms` on every public declaration. Read every emitted formula when a Scribe changes. Use the shared Lean build lock for every Lean invocation.
5. **Return.** `verdict: mirror-ready` with current readings, or `open` with exact readings. Stop before any freeze door.

'''
    mirror_head = f'''# Pre-freeze mirror check, round {rnd} — lane `op-{lane}`

First check every blocking finding in `{env}` against continuation {suffix}; then apply the full checklist below. No freeze door may run.

**Orchestrator adjudication (binding):**
- A probe that exhausts its budget names no defect. Report incomplete probes under `assumed_unverified`.
- A blocking reuse finding needs a compiled owner route.
- Preregistered binding definitions are literal and exempt from reuse rewriting.
- Return `approve` or `reject`. The `comment` verdict is forbidden. Checks that cannot finish within the time box go under `assumed_unverified` and do not withhold approval.

'''
    Path(out).write_text(head + rest)
    Path(out_mirror).write_text(mirror_head + mirror_rest)
    print('CONT_OK', lane, suffix, len(findings), build_targets)


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        from continuation_selftest import run
        sys.exit(run('mirrorfix_cont'))
    sys.exit(entry(main, minimum=10))
