#!/usr/bin/env python3
from common import fail
'Portable implb head. See the openproblem README for inputs.'
from common import BUILD_SCOPE, Context, REPO, TOOLS, entry, lane_spec
from pathlib import Path
import shlex


def purge_command(path):
    return 'python3 ' + shlex.quote(str(path)) + ' "$(git rev-parse --show-toplevel)" --delete'

def main(argv):
    ctx = Context()
    import json, re, sys
    S = str(ctx.scratch)
    L = argv[1]
    d = lane_spec(f'{S}/lanes/{L}.json')
    t = d['target_md']
    issue = re.search('issue \\*\\*#(\\d+)\\*\\*', t).group(1)
    kind = 'Refuted' if 'Refuted' in re.search('Settlement: \\*\\*(\\w+)\\*\\*', t).group(0) else 'Proved'
    mod = d['module']
    dossier = re.search('`Problems/([a-z0-9-]+)\\.md`', t)
    if not dossier:
        fail(13, 'NO_DOSSIER_NAME')
    note = re.search('\\*\\*Library note\\.\\*\\* (One note for [^,.(]+)', t)
    note = note.group(1).replace('One note for', 'the Library note for').strip() if note else 'the Library note'
    gen = re.search('`generality: ([GIE])`', t)
    gen = gen.group(1) if gen else 'I'
    module_file = Path(d['worktree']) / (mod + '.lean')
    if module_file.is_file():
        header_gen = re.search(r'^\s*generality: ([GIE])\s*$', module_file.read_text(), re.M)
        if header_gen:
            gen = header_gen.group(1)
    if kind == 'Refuted':
        util = '`utility: kind=certified-instance; basis=refutes=…`'
        exempt = ' The designated refutation `result` is exempt (CLAUDE.md §3.9).'
    else:
        util = '`utility: none`'
        exempt = ''
    PURGE = purge_command(TOOLS / 'briefgen/purge_stale_fib.py')
    out = f"""# Stage B — lane `op-{L}` (#{issue}): freeze the settling {('refutation' if kind == 'Refuted' else 'module')} and open a Draft PR\n\n{BUILD_SCOPE}\n\n- **SDK host.** In the same shell as every `make`, first run `export DOTNET_ROOT="$(dirname "$(python3 -c 'import os,shutil;print(os.path.realpath(shutil.which("dotnet")))')")"`.\n- **Worktree.** `{d['worktree']}`, branch `{d['branch']}`.\n- **Delivery.** All uncommitted; the new files are:\n  - the settling module `{mod}.lean` (`open-problem-resolution (#{issue}; {kind})`, `generality: {gen}`, {util});\n  - one Scribe per module;\n  - the Reg mirrors, if any registration decodes;\n  - {note} (check that no other note on dev owns the DOI).\n- **Envelopes.** The Stage A envelope and the approving mirror are named in the "Pre-freeze review identity" block below.\n- **Stale report cache.** Before the first freeze door, run `{PURGE}` once in this worktree, and report its `PURGE_STALE_FIB` line. If a freeze door still fails with `fib.invalid_partition`, run it once more and retry the door once.\n- **Doors.**\n  1. Sync with dev (the block below), merging `origin/dev` first.\n  2. Run the reuse sweep against fresh `origin/dev`, then `make emit` twice (the second changes 0 files), and commit the Phase A source.\n  3. **Freezes, in import order,** each with `B="$(git merge-base HEAD origin/dev)"` pinned once before the first door:\n     - the settling freeze: `make deposit-uncovered GID={mod}.result BASE="$B"`;\n  - Commit all door output in ONE builder commit, with no commit between the doors. Never hand-edit `Golden/**`.\n- **Escape audit.** Every new public theorem and every published owner declaration is an audit target.{exempt} Report whether each Reg registration decodes at the delivered head from the scoped report, and read its `DTR-*` finding from the required CI `current` job of the pushed head (`gh run view <run-id> --log --job <current-job-id>`, the `DTR-` lines; report the run id and job id); until that reading exists the registration is pending. Never write `declared_validated` without that CI reading. Every target without a `declared_validated` registration goes in one unfinished-audit issue, linked from each module comment, the dossier and the PR body.\n- **Dossier.** `Problems/{dossier.group(1)}.md`, with one `OpenProblemResolutionClaim` ({kind}) on the settling node. Its Triage covers every item of the lane target and gives the literature status (completeness `ASSUMED-UNVERIFIED`).\n- **PR body.**\n  - The judgement table has one row per public theorem of the delivered modules: `proof_shape`, `escape_witness`, consumers, and direct frozen dependencies. Generate it by script from the compiled proof terms as owning-module GID + full Lean name + declaration `statement_id`.\n  - Also give each module's `admission_basis`.\n  - The provenance carries the mixing sentence exactly: "Review mixing: each round uses three codex-cli verification seats that run one after the other on the same worktree, each blind to the other seats' results within the round; every verdict counts and a reject opens a new round; no model-diversity claim is made."\n  - {ctx.provenance}\n  - The body states only current results; no implementation chronology.\n- **Review layout.** The standing section is exactly the block in the procedure below: the round-1 zero-tally line and the round-1 layout line. Open the PR with `DRAFT=1`.\n- **Push.** Run `LEAN4_GUARDRAILS_BYPASS=1 git push origin {d['branch']}`, then verify with `git ls-remote`. Never force-push.\n\n"""
    open(f'{S}/briefs/implb-{L}-r1.head.md', 'w').write(out)
    print('HEAD_OK', L, issue, kind, mod)
if __name__ == '__main__':
    import sys
    sys.exit(entry(main, minimum=1, maximum=1))
