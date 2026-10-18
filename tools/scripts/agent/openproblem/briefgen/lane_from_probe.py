#!/usr/bin/env python3
"""Usage: lane_from_probe.py KEY ISSUE SETTLEMENT MODULE WORKTREE FLIGHT DOSSIER_SLUG COMMIT_SUBJECT."""
import json
from pathlib import Path
import re
import subprocess
import sys
from common import Context, entry, fail, load, name


def main(argv):
    ctx = Context(required=('gh',))
    key, issue, settle, module, wt, flight, slug, subject = argv[1:]
    name(key)
    if not re.fullmatch(r'[1-9][0-9]*', issue):
        fail(13, 'positive issue number required')
    if settle not in ('Proved', 'Refuted'):
        fail(13, 'settlement must be Proved or Refuted')
    if not re.fullmatch(r'D5(?:/[A-Za-z_][A-Za-z0-9_]*)+', module):
        fail(13, 'one extension-free D5 module path required')
    if not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', slug):
        fail(13, 'invalid dossier slug')
    if not subject.strip() or '\n' in subject or '\r' in subject:
        fail(13, 'single-line commit subject required')
    tree = Path(wt)
    tree = (tree if tree.is_absolute() else ctx.main / tree).resolve()
    if not tree.is_dir():
        fail(11, 'worktree missing: ' + str(tree))
    wt = str(tree)
    env = ctx.result(flight)
    c = load(env).get('conclusion')
    if not isinstance(c, dict) or not c.get('module_plan') or 'triage' not in c:
        fail(13, 'probe conclusion requires module_plan and triage')
    if not isinstance(c['module_plan'], (list, dict)) or not isinstance(c['triage'], (list, dict)):
        fail(13, 'invalid module_plan or triage')
    scratch_files = c.get('scratch_files') or []
    if not isinstance(scratch_files, list) or any(not isinstance(f, dict) or not isinstance(f.get('path'), str) for f in scratch_files):
        fail(13, 'scratch_files must contain named paths')
    response = subprocess.run(['gh', 'issue', 'view', issue, '-R', ctx.slug, '--json', 'title', '-q', '.title'], capture_output=True, text=True)
    if response.returncode:
        fail(16, 'cannot read preregistration title')
    title = response.stdout.strip()
    if not title:
        fail(13, 'empty preregistration title')
    short = title.split(': ', 1)[1] if ': ' in title else title
    scratch = '\n'.join(f"  - `{f['path']}`: {f.get('role', '')}" for f in scratch_files)
    plan = json.dumps(c['module_plan'], ensure_ascii=False, indent=1)
    triage = json.dumps(c['triage'], ensure_ascii=False, indent=1)
    target = f"""Open problem: {short}. Settlement: **{settle}**.

Preregistration: GitHub issue **#{issue}**. It holds the verbatim source, the statement with its proof, the binding Lean conventions, the experiment readings and the literature screen; read it with `gh issue view {issue} --comments`. The settling module carries `admission_basis: open-problem-resolution (#{issue}; {settle})`.

**Probe result (the proof to port).** The probe reports kernel-checking the settling `result` with the three standard axioms only; this generator does not verify Lean evidence.
**Scratch sources** (paths reported by the probe):
{scratch}
- **Envelope.** `{env}` is a binding input: `module_plan`, `proof_shapes`, `reuse_table`, `cost_readings`, `items`, `obstructions` and `triage`.

**Modules (binding plan from the probe).** Follow the envelope's `module_plan` (reproduced here):
```json
{plan}
```
- **The settling module** is `{module}`. Its header has the plan's `generality` and `utility`, and the admission basis above.
- **Common rules.**
  - Namespaces follow the files.
  - Every module stays within 1000 lines, 600 s and 9 GB; measure each one.
  - Imports are precise, and each module imports where it consumes.
  - Helpers are private and consumed, or public only where another delivered module consumes them. Report `proof_shape` per declaration, with consumers.
  - Where the plan publishes a frozen private owner, keep its statement and proof. Re-pin it, and run the binding "Frozen importers of published owners" block. Each published owner `theorem`/`lemma` is a new public theorem for the §3.9 escape audit: attempt its Reg registration, or list it by full name in the unfinished-audit issue and name it in the PR body.

**Escape audit.** Every new public theorem is an audit target, except a refutation `result` named by `utility basis=refutes`. For each target, attempt Reg registration, or list it in one unfinished-audit issue linked from the module comments, the dossier and the PR body.

**Reuse sweep.** Before mirror-ready, check every definition by body (generic owners included, concrete data exempt), every helper and every closed local `have` against frozen D5 owners (private included) and pinned Mathlib. The preregistered conventions are literal and exempt from rewriting.

**Delivery shape.**
- **Library note.** One note for the source (DOI, or arXiv URL with version, as on #{issue}). Put it in a Library directory with room: count first, because directories at 96 entries are full.
- **Scribe.** One Scribe per delivered module. The settling node uses `FromRepo(<the note>)`, and the `result` node displays the expanded claim.
- **Dossier.** Stage B adds `Problems/{slug}.md`, with one `OpenProblemResolutionClaim` ({settle}).

**Triage items** (each with one evidence kind per claim), from the probe's `triage` and the issue's "Beyond the settlement" section:
```json
{triage}
```
- **Experiment.** Cite the experiment named on #{issue} (repository, commit, sha256, exit code); embed no program text.
- **Literature.** As recorded on #{issue}; completeness is `ASSUMED-UNVERIFIED`.
"""
    spec = {"lane": key, "title": f"{short} ({settle.lower()})", "worktree": wt,
            "branch": f"lane/math/op-{key}", "module": module, "gid": module + ".result",
            "commit_subject": subject, "target_md": target}
    lanes = ctx.scratch / 'lanes'
    lanes.mkdir(parents=True, exist_ok=True)
    for filename, content in ((key + '.json', json.dumps(spec, ensure_ascii=False, indent=1) + '\n'),
                              (key + '.target.md', target)):
        tmp = lanes / (filename + '.tmp')
        tmp.write_text(content)
        tmp.replace(lanes / filename)
    print('LANE', key, len(target))


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        from port_selftest import run
        sys.exit(run('lane_from_probe'))
    sys.exit(entry(main, minimum=8, maximum=8))
