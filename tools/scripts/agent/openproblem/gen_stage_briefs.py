#!/usr/bin/env python3
'Generate portable open-problem briefs. See README.md for modes and inputs.'
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / 'briefgen'))
from common import BUILD_SCOPE, Context, entry, fail

def render_mirror(template, lane, worktree, branch, module):
    import re
    values = {'__LANE__': lane, '__WORKTREE__': worktree,
              '__BRANCH__': branch, '__MODULE__': module}
    def replace(match):
        token = match.group(0)
        if token not in values:
            fail(13, f'unknown mirror-check template token: {token}')
        return values[token]
    return re.sub(r'__[A-Z][A-Z0-9_]*__', replace, template)

def legacy(argv):
    ctx = Context(argv[1])
    import sys, pathlib, re
    here = pathlib.Path(__file__).resolve().parent
    sp = pathlib.Path(argv[1])
    lane, wt, branch, module = argv[2:6]
    nyx = argv[6] if len(argv) > 6 else ''
    if nyx and nyx not in ('architecture', 'quality'):
        fail(13, f'NYXID_SEAT must be architecture or quality, got {nyx!r}')
    src = sp / 'briefs' / f'impl-op-w1-{lane}.md'
    for required in (src, here / 'templates' / 'impl-base-brief.md', here / 'templates' / 'mirror-check-template.md'):
        if not required.is_file():
            fail(13, f'missing required input: {required}')
    t = src.read_text()
    i = t.index('## Steps')
    j = t.index('## Result envelope')
    pre, steps, env = (t[:i], t[i:j], t[j:])
    m = re.search('\\n5\\. \\*\\*Deposit / cover\\*\\*', steps)
    assert m, 'step 5 anchor not found'
    stepsA = steps[:m.start()]
    stepsB = '## Steps (Stage B — doors)\n' + steps[m.start() + 1:]
    stepsB = stepsB.replace('\n6. ONE builder commit', "\n5′. **Anchor cover (mandatory):** `make deposit` freezes the anchor theorem but does NOT write the anchor atom's own coverage edge — run `make cover ATOM_ID=<anchor atom> GID=<anchor GID>` after the deposit and verify every target atom (anchor included) is `absorbed-closed` before committing (`ls Meta/Digestion/backfill/<source>/absorbed-closed/ | grep -c <id>`); a lane whose anchor stays residual-open is incomplete.\n6. ONE builder commit", 1)
    stopA = '\n4′. **STOP HERE (Stage A ends before any freeze), and emit in PHASE A SHAPE.** Do NOT run `make deposit`, `make cover`, `git commit`, `git push` or `make pr-open`.\n\n**If this lane\'s Scribe carries an `OpenProblemResolutionClaim`, that node must NOT be in the tree yet, and the `Problems/` dossier must not exist yet.** Both reference a declaration that has to already be a member of the frozen state, and freezing happens inside `make deposit`. Emitting with them present makes `make emit` exit 2 with `invalid-problem-resolution-source` (host module is not a member of frozen state) and `dangling-problem-slug`; **no Stage-A state change can satisfy that validator**, so this is an ordering contract rather than something to work around. Write the claim node and the dossier in Stage B, after the door has frozen the host.\n\n**A `Library/` note is the opposite case: `FromLiterature` needs it present during emission**, or `make emit` reports `dangling-literature-reference`. Write it in Stage A.\n\nLeave the new files UNCOMMITTED in the worktree. What MUST be present: `<module>.lean`, `Blueprint/<module>.scribe.cs`, the emitted `Blueprint/<module>.md`, and every file any `*Ref.Create(...)` in the Scribe names — a `LibraryNoteRef` needs its `Library/` note on disk. Nothing tracked may be modified. **Do not delete an artifact to satisfy a file count**: emission readings describe the tree they ran on, so removing a note after a green `make emit` leaves exit codes that are no longer true of what you hand over, and the envelope cannot show that.\n\n**The second comment block is part of the handover.** Immediately after the 7-line header the module must carry a second comment block recording, per public theorem, `proof_shape:`, `escape_witness:`, `admission_basis:` and `Direct frozen dependencies:` (the values the brief\'s HEADER AND ADMISSION section names). Before returning, run `grep -c \'admission_basis:\' <module>.lean` and report the count: it must be `1`. Also report `grep -cE \'^private (theorem|lemma)\' <module>.lean` and, for every remaining `private def`, its `#check` type: a proposition-valued `private def` is a theorem for every §3.2 purpose (see the base brief) and must be classified/listed or inlined. The judgement-form seat requires this block under condition (b) of the open-problem-resolution basis.\n\nVerify the handover, not the run: after the second `make emit`, re-read `git status`, confirm each `*Ref.Create` target file exists on disk, and check that the emitted `.md` renders what that reference is for — a `LibraryNoteRef` renders as a `*Citation.*` line carrying the author, year, title and URL, **not** as the note\'s slug, so grepping for the slug is the wrong check and will read as a failure on a correct delivery. `make emit` must exit 0 on both runs, the second reporting 0 changed blueprints, **at the tree you are leaving**. A read-only mirror-check seat will now compare the mirror against the Lean statements symbol by symbol; a Stage-B seat will run the doors afterwards. Return the Stage-A envelope now.\n\n## Result envelope (Stage A)\n`conclusion` = {"verdict":"mirror-ready|open|already-landed","module_path":"…","theorem_names":[…],"print_axioms":{…},"exit_codes":{"make_lean":n,"make_emit":n,"scribe_corpus_test":n},"public_statements":[{"name":"…","statement":"<full Lean statement text to := by>"}],"mirror_selfcheck":{"parenthesized_only":true|false,"binder_body_symbols":true|false,"nat_div_not_fraction":true|false,"coercions_mirrored":true|false,"relation_in_group_items":false},"proof_shape":{…},"escape_witness":"…","admission_basis":"…","search_trace":[…],"collision_check":"…","fidelity_gate":{…},"assumed_unverified":[…],"open_reasons":[…],"visible_inputs":[…]}, plus `log_ref`.\n'
    A = pre.replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)', '(STAGE A: module + mirror only — no doors; a mirror-check seat and a Stage-B doors seat follow)') + stepsA + stopA
    B_head = pre.split('\n', 1)[0].replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)', '(STAGE B: doors only — the module, mirror and emitted md are ALREADY in the worktree, uncommitted, and passed a read-only mirror check; run the doors, one builder commit, late dedupe, push, PR)')
    B_intro = f"""\n\nYou are the Stage-B `implementation_worker` (codex-cli). Worktree `{wt}` on branch `{branch}` already contains the UNCOMMITTED, mirror-checked `{module}.lean`, `Blueprint/{module}.scribe.cs` and emitted `Blueprint/{module}.md` (`git status --porcelain` shows them). Do NOT rewrite the mathematics or the mirror except for the exact fixes listed under "## Mirror-check fixes" below (if that section is empty, touch nothing). Re-run `make lean LEAN_TARGETS="<the delivered modules and every frozen module you re-pin, dotted>"` (EXIT=0) and `make emit` (EXIT=0) once to confirm the tree, then execute the doors below exactly. Follow `skills/codex-formalize/SKILL.md` Steps 7–8 and `CLAUDE.md` 5⁗. Judge by bare exit codes. Return exactly one result envelope (the original contract, appended).\n\n## Emission order around the door — read this before you touch anything\n\nStage A left the tree in **Phase A shape**: the module, the mirror **without** any `OpenProblemResolutionClaim`\nnode, the emitted `.md`, and the `Library/` note if the lane cites literature. Keep it that way through the door.\n\n- **Phase A (before the freeze).** With no claim node and no `Problems/` dossier in the tree: `make lean LEAN_TARGETS="<the delivered modules and every frozen module you re-pin, dotted>"` EXIT=0,\n  `make lean-report-scoped LEAN_TARGETS="<the same list>"` EXIT=0, `make emit` twice with the second reporting 0 changed blueprints, then commit the\n  source, then — **in the same command as the door** — verify `git merge-base --is-ancestor origin/dev HEAD`,\n  run the late dedupe, and run the deposit. A stop at the ancestry check writes no frozen state\n  (`frozen_state_written: false`, zero `Golden/Frozen` changes) and is a CONTINUATION at the next attempt, not a\n  lane redo.\n- **Phase B (after the freeze).** Now add the `OpenProblemResolutionClaim` node to the Scribe and write the\n  `Problems/` dossier whose motivation GID names the now-frozen declaration. `make emit` twice again, second run\n  0 changed. Then ONE builder commit carrying the door's delta — the module state record, the new\n  dossier and the re-emitted mirror — followed by push and `make pr-open AUTO_MERGE=0`.\n\nTwo commits, in that order. If you find yourself wanting to emit the claim before the deposit, re-read this: the\nvalidator is asking for a frozen host, and only the door can give it one.\n\n## Mirror-check fixes\n<<MIRROR_FIXES>>\n\n\n\n**Render check after ANY Stage-B mirror change:** if you add or edit Describe nodes here, then after `make emit` run `grep -n -E '&&|\\|\\||==|!=|\\bdecide\\b.*&&' Blueprint/<module>.md` (must be empty — Lean Boolean `&&`/`||`/`==` must be rendered as `∧`/`∨`/`=` inside `Parenthesized`), re-read every new formula, and inspect the scoped door readings: a line `markdown red <your module>.md:…` (KaTeX parse error) or any check naming your module is a STOP-and-fix condition BEFORE `make deposit`; unrelated locale/observe noise is not. """
    gm = re.search('## GoalArtifact.*?(?=\\n## |\\Z)', pre, re.S)
    goal = gm.group(0) + '\n\n' if gm else ''
    base = (here / 'templates' / 'impl-base-brief.md').read_text()
    extra = ''.join(re.findall('\\n6[′″]\\. \\*\\*.*?(?=\\n[0-9]+[′″]?\\. |\\n## )', base, re.S))
    stepsB = stepsB.replace('\n7. `git push', extra + '\n7. `git push', 1) if '6′.' not in stepsB else stepsB
    layout = ''
    if nyx:
        other = 'quality' if nyx == 'architecture' else 'architecture'
        layout = f"""\n## Round-1 review layout (drawn by the orchestrator before this dispatch — write it into the PR body)\n\nThe first-published standing table lists the CURRENT round's seats and carriers as a fact: `{nyx} nyxid-oracle /\nChatGPT Pro, {other} codex-cli, tests codex-cli`, at the delivered head, with a zero tally, `Carried-forward\napprovals: none.` and `Disagreement adjudication: none.` Do not write "not established"; the assignment is this one.\nDo not describe the standing table as empty, and do not say what happens when a round closes: a sentence such as\n"the table above is empty until a round closes" is process narration and must be omitted.\n\n"""
    B = B_head + '\n\n' + BUILD_SCOPE + B_intro + goal + layout + stepsB + env
    (sp / 'briefs' / f'impl-op-w1-{lane}.stageA.md').write_text(A)
    (sp / 'briefs' / f'impl-op-w1-{lane}.stageB.md').write_text(B)
    mc = render_mirror((here / 'templates' / 'mirror-check-template.md').read_text(), lane, wt, branch, module)
    (sp / 'briefs' / f'mirror-check-{lane}.md').write_text(mc)
    print('stageA', len(A), 'stageB', len(B), 'mirror-check', len(mc))

def main(argv):
    if argv[1:2] == ['--lane-spec']:
        import subprocess
        if len(argv) != 4:
                        fail(10, '--lane-spec LANE NYXID_SEAT')
        return subprocess.call(['/bin/bash', str(Path(__file__).resolve().parent / 'briefgen/stages.sh'), *argv[2:]])
    return entry(legacy, argv, minimum=5, maximum=6)
if __name__ == '__main__':
    sys.exit(entry(main))
