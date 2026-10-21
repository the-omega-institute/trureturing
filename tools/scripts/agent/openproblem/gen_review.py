#!/usr/bin/env python3
'Generate portable open-problem briefs. See README.md for modes and inputs.'
import sys
import re
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / 'briefgen'))
from common import Context, entry, fail

def render_review(template, values):
    def replace(match):
        token = match.group(0)
        if token not in values:
            fail(13, f'unknown review template token {token!r}')
        return values[token]
    return re.sub(r'__[A-Z][A-Z0-9_]*__', replace, template)

def legacy(argv):
    ctx = Context(required=('gh',))
    import sys, subprocess, pathlib, re
    if len(argv) != 8:
        sys.exit(__doc__)
    here = pathlib.Path(__file__).resolve().parent
    out_dir = ctx.scratch / 'briefs'
    lane, pr, branch, worktree, impl_env, target_file, nyx_seat = argv[1:8]
    if nyx_seat not in ('architecture', 'quality'):
        fail(13, f'NYXID_SEAT must be architecture or quality, got {nyx_seat!r}')
    tpl_path = here / 'templates' / 'review-template.md'
    base_brief = here / 'templates' / 'impl-base-brief.md'
    for required in (tpl_path, base_brief, pathlib.Path(target_file)):
        if not required.is_file():
            fail(13, f'missing required input: {required}')
    tpl = tpl_path.read_text()
    ga_match = re.search('```yaml\\n(.*?)\\n```', base_brief.read_text(), re.S)
    if ga_match is None:
        fail(13, f'no yaml GoalArtifact fence found in {base_brief}')
    ga = ga_match.group(1).rstrip()
    out_dir.mkdir(parents=True, exist_ok=True)
    head = subprocess.check_output(['git', '-C', worktree, 'rev-parse', 'HEAD'], text=True).strip()
    files = subprocess.check_output(['git', '-C', worktree, 'diff', '--name-status', 'origin/dev...HEAD'], text=True).strip()
    title = subprocess.check_output(['gh', 'pr', 'view', pr, '-R', ctx.slug, '--json', 'title', '--jq', '.title'], text=True).strip()
    target = pathlib.Path(target_file).read_text().strip()
    biases = {'architecture': 'boundaries, contracts, coupling, maintainability: module placement (natural owner bucket, capacity read from the owner file), import minimality (every import consumed; no false ledger edge), namespace/GID = path, generality tag vs weakest import, Blueprint mirror shape and formula DSL (visible grouping MUST be `Parenthesized` — `Grp` emits TeX braces that print no parentheses; no relation node inside `LatexGroup.Items`, an uncovered corpus shape that turns CI red), no second source of truth (def-level duplicate search on FRESH current dev after `git fetch origin`), dependency edges derived from actual source imports; 5⁗ escape witness on the LIVE proof path.', 'quality': 'fidelity/non-hollowness: statements byte-faithful to the obligation atoms (echo table; `make show-atom` is authority); DEFINITION fidelity: every object the atom DEFINES by a formula (a kernel, an energy, a count, a predicate) must appear in Lean either as that literal defining expression or with a PUBLIC identity theorem equating the Lean definition to the atom expression, and the covered statement must refer to the atom-defined object — a mathematically equivalent replacement definition without an addressable public identity is a fidelity FAIL; no weakening/strengthening/added hypotheses; conclusion not True/tautology; both sides of every equation independently anchored; read the EMITTED `.md` value by value — every rendered parenthesis/grouping must match the atom (a `Grp`-rendered `n·(xy+xz+yz)` reads `nxy+xz+yz`); no private helper restating a frozen theorem; proof_shape/escape_witness/admission_basis per public theorem audited against the elaborated proof; companions have honest directed edges; PR body readings (exit codes, HEAD, #print axioms) and provenance triple present.', 'tests': 'verification strength: RUN `make lean` (or `make lean LEAN_TARGETS="<module>"`) and `make emit` in the worktree at HEAD and report exit codes; `#print axioms` for every public theorem (std3 only); `git fetch origin` FIRST, then re-run the def/theorem duplicate greps and conclusion-shape searches on the FRESH origin/dev; run the Scribe `FormulaCorpusInventoryTests` and `DocumentDiscoveryTests` and report exit codes; verify every covered atom (INCLUDING the atom of the deposit anchor itself) moved to absorbed-closed and that deposit+covers sit in ONE builder commit; verify the state record and ledger moves are door output only (no hand edits under Meta/Digestion or Golden/Frozen); Scribe test subset for the document; mutation sanity (does deleting the claimed escape witness break the main theorem? — reason from the proof term, do not edit tracked files).'}
    for role in ['architecture', 'quality', 'tests']:
        role_template = tpl
        review_worktree = worktree
        if role == nyx_seat:
            review_worktree = 'n/a for this carrier — read the PR diff at https://github.com/the-omega-institute/trureturing/pull/' + pr + '/files and the raw files at https://raw.githubusercontent.com/the-omega-institute/trureturing/' + head + '/<path>; local paths are unreadable references'
            role_template = role_template.replace('Return exactly one result envelope (shape at the end / contract appended).', 'Return EXACTLY one JSON object inside a single ```json fence and nothing else (shape at the end); keep the reply under 12,000 characters.')
        t = render_review(role_template, {
            '__ROLE__': role, '__PR__': pr, '__TITLE__': title,
            '__GOAL_ARTIFACT__': ga, '__BRANCH__': branch, '__HEAD__': head,
            '__TARGET__': target, '__IMPL_ENVELOPE__': impl_env,
            '__FILES__': '\n' + files, '__BIAS__': biases[role],
            '__WORKTREE__': review_worktree,
        })
        out = out_dir / f'review-{lane}-{role}.md'
        out.write_text(t)
        print('wrote', out.name, len(t.encode()), 'bytes')

def main(argv):
    if argv[1:2] in (['--codex3'], ['--pipeline']):
        import subprocess
        import shutil
        from common import fail, name
        ctx = Context(required=('gh',))
        if len(argv) != 9:
            fail(10, '--codex3|--pipeline LANE PR BRANCH WORKTREE ENVELOPE TARGET ROUND|NYXID_SEAT')
        lane, pr, branch, wt, envelope, target, last = argv[2:]
        name(lane)
        script = str(Path(__file__).resolve().parent / 'briefgen/review.sh')
        if argv[1] == '--pipeline':
            return subprocess.call(['/bin/bash', script, lane, pr, branch, wt, envelope, target, last])
        if not last.isdigit() or int(last) < 1:
            fail(13, 'positive round required')
        for nyx, roles in [('quality', ('architecture', 'tests')), ('architecture', ('quality',))]:
            rc = subprocess.call(['/bin/bash', script, lane, pr, branch, wt, envelope, target, nyx])
            if rc:
                return rc
            for role in roles:
                source = ctx.scratch / 'briefs' / f'review-{lane}-{role}.md'
                out = source.with_name(f'review-{lane}-{role}-r{last}.md')
                text = source.read_text()
                if '## Import rule (binding, every lane)' not in text:
                    text += ctx.block('mirror-import-rule-block.md').read_text()
                out.write_text(text)
        return 0
    return entry(legacy, argv, minimum=7, maximum=7)
if __name__ == '__main__':
    sys.exit(entry(main))
