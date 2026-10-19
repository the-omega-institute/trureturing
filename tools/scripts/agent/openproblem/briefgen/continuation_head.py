#!/usr/bin/env python3
'Portable continuation head. See the openproblem README for inputs.'
from common import Context, REPO, entry

def main(argv):
    ctx = Context()
    import json, sys
    S = str(ctx.scratch)
    lane, issue, suf, mf, wt, out = argv[1:7]
    owners = argv[7:]
    env = str(ctx.result(mf))
    c = json.load(open(env))['conclusion']
    bf = c['blocking_findings']

    def s(x):
        return x if isinstance(x, str) else json.dumps(x, ensure_ascii=False)
    items = []
    for i, f in enumerate(bf, 1):
        fl = s(f.get('file_line') or f.get('locations') or '')
        ev = f.get('compiled_route') or f.get('evidence') or ''
        evs = f' (evidence: {s(ev)[:500]}; adapt only as far as the compiler needs)' if ev else ''
        items.append(f"   {i}. **`{fl[:300]}`.** {s(f.get('claim', ''))}\n      - **Fix{evs}.** {s(f.get('fix', ''))}")
    own = ', '.join((f'`{o}`' for o in owners))
    head = f"""# Stage A continuation {suf} — lane `op-{lane}` (#{issue}): {len(bf)} mirror findings plus the self-sweep, then stop at mirror-ready (binding; overrides every earlier head below)\n\nThe pre-freeze mirror (`{env}`, verdict reject) found {len(bf)} blocking findings; read its `blocking_findings` (exact fix texts, routes) before editing.\n\n1. **Preconditions.** The Stage A delivery is uncommitted in `{wt}` on fresh `origin/dev` (`git fetch origin dev && git merge --ff-only origin/dev` first if dev moved; stash/pop around it if needed). Otherwise stop with `open` and the readings.\n2. **The findings.** Apply all of them:\n{chr(10).join(items)}\n3. **Touched frozen owners.** A touched frozen owner may differ from `origin/dev` only by removed `private` keywords, moved definitions and required diagnostic deletions: no comment, label or audit-sentence edits in it (audit disclosures live in the new modules, the dossier and the PR body). Check with `git diff origin/dev -- <owner>`.\n4. **Self-sweep.** Run the self-sweep below over every declaration this delivery adds or edits, and apply every hit.\n5. **Verify every touched module**, each with EXIT: `make lean LEAN_TARGETS="<every module the delivery changes or adds>"`{(' (the touched owners ' + own + ' included)' if own else '')}; `header-check.sh` for every new module; `#print axioms result` in scratch; the Scribe build and `FormulaCorpusInventoryTests`.\n6. **Stop.** Leave the delivery uncommitted. Stop with `verdict: mirror-ready` and the usual Stage A envelope, including the self-sweep table. Run no freeze door, commit or push.\n\n"""
    head += open(ctx.block('self-sweep-block.md')).read() + '\n---\n\n'
    open(out, 'w').write(head)
    print('CONT_HEAD_OK', len(bf), out)

if __name__ == "__main__":
    import sys
    sys.exit(entry(main, minimum=6, maximum=None))
