#!/usr/bin/env python3
"""Split an implementation brief into Stage A (module + mirror + make lean/emit, STOP before any door) and
Stage B (doors: deposit/cover, one builder commit, late dedupe, push, PR). Also fills the mirror-check brief.
usage: gen_stage_briefs.py SCRATCHPAD LANE WORKTREE BRANCH MODULE_RELPATH(no ext, e.g. D5/S1/X/Y) [NYXID_SEAT]
writes briefs/impl-op-w1-<lane>.stageA.md, .stageB.md, mirror-check-<lane>.md
NYXID_SEAT (architecture|quality) is the round-1 review seat the orchestrator has ALREADY drawn (od /dev/urandom,
README step 9); the Stage-B brief tells the seat to write that layout into the first-published standing table,
because "seat assignment is not established at first publication" was a blocking §5.2 finding (#8511). Omitted
means the Stage-B brief carries no layout and the orchestrator must edit the body before the first round.
The only input read from SCRATCHPAD is briefs/impl-op-w1-<lane>.md; the base brief and the mirror-check
template are read from this script's own tracked templates/ directory. Missing inputs exit 1 with the path."""
import sys,pathlib,re
# Tracked templates live next to this script, never in the caller's scratchpad: a wiped scratchpad
# must cost nothing but the one lane brief the caller wrote (case #6220, the same reason gen_review.py
# reads its template and GoalArtifact from here).
here=pathlib.Path(__file__).resolve().parent
sp=pathlib.Path(sys.argv[1]); lane,wt,branch,module=sys.argv[2:6]
nyx=sys.argv[6] if len(sys.argv)>6 else ''
if nyx and nyx not in ('architecture','quality'):
    sys.exit(f'NYXID_SEAT must be architecture or quality, got {nyx!r}')
src=sp/'briefs'/f'impl-op-w1-{lane}.md'
for required in (src, here/'templates'/'impl-base-brief.md', here/'templates'/'mirror-check-template.md'):
    if not required.is_file():
        sys.exit(f'missing required input: {required}')
t=src.read_text()
i=t.index('## Steps'); j=t.index('## Result envelope')
pre,steps,env=t[:i],t[i:j],t[j:]
# split steps: everything up to and including step 4 → stage A; step 5.. → stage B
m=re.search(r'\n5\. \*\*Deposit / cover\*\*',steps); assert m, 'step 5 anchor not found'
stepsA=steps[:m.start()]; stepsB='## Steps (Stage B — doors)\n'+steps[m.start()+1:]
stepsB=stepsB.replace('\n6. ONE builder commit','\n5′. **Anchor cover (mandatory):** `make deposit` freezes the anchor theorem but does NOT write the anchor atom\'s own coverage edge — run `make cover ATOM_ID=<anchor atom> GID=<anchor GID> BASE=origin/dev` after the deposit and verify every target atom (anchor included) is `absorbed-closed` before committing (`ls Meta/Digestion/backfill/<source>/absorbed-closed/ | grep -c <id>`); a lane whose anchor stays residual-open is incomplete (#5480, #5504 needed orchestrator repairs).\n6. ONE builder commit',1)
stopA='''
4′. **STOP HERE (Stage A ends before any freeze), and emit in PHASE A SHAPE.** Do NOT run `make deposit`, `make cover`, `git commit`, `git push` or `make pr-open`.

**If this lane's Scribe carries an `OpenProblemResolutionClaim`, that node must NOT be in the tree yet, and the `Problems/` dossier must not exist yet.** Both reference a declaration that has to already be a member of the frozen state, and freezing happens inside `make deposit`. Emitting with them present makes `make emit` exit 2 with `invalid-problem-resolution-source` (host module is not a member of frozen state) and `dangling-problem-slug`; **no Stage-A state change can satisfy that validator**, so this is an ordering contract rather than something to work around. Write the claim node and the dossier in Stage B, after the door has frozen the host.

**A `Library/` note is the opposite case: `FromLiterature` needs it present during emission**, or `make emit` reports `dangling-literature-reference`. Write it in Stage A.

Leave the new files UNCOMMITTED in the worktree. What MUST be present: `<module>.lean`, `Blueprint/<module>.scribe.cs`, the emitted `Blueprint/<module>.md`, and every file any `*Ref.Create(...)` in the Scribe names — a `LibraryNoteRef` needs its `Library/` note on disk. Nothing tracked may be modified. **Do not delete an artifact to satisfy a file count**: emission readings describe the tree they ran on, so removing a note after a green `make emit` leaves exit codes that are no longer true of what you hand over, and the envelope cannot show that.

**The second comment block is part of the handover.** Immediately after the 7-line header the module must carry a second comment block recording, per public theorem, `proof_shape:`, `escape_witness:`, `admission_basis:` and `Direct frozen dependencies:` (the values the brief's HEADER AND ADMISSION section names). Before returning, run `grep -c 'admission_basis:' <module>.lean` and report the count: it must be `1`. Also report `grep -cE '^private (theorem|lemma)' <module>.lean` and, for every remaining `private def`, its `#check` type: a proposition-valued `private def` is a theorem for every §3.2 purpose (see the base brief) and must be classified/listed or inlined. The judgement-form seat rejects a module without it (condition (b) of the open-problem-resolution basis; misawa33 and zhangd were both rejected for this omission on 2026-09-18), and the fix then costs a Stage-B edit.

Verify the handover, not the run: after the second `make emit`, re-read `git status`, confirm each `*Ref.Create` target file exists on disk, and check that the emitted `.md` renders what that reference is for — a `LibraryNoteRef` renders as a `*Citation.*` line carrying the author, year, title and URL, **not** as the note's slug, so grepping for the slug is the wrong check and will read as a failure on a correct delivery. `make emit` must exit 0 on both runs, the second reporting 0 changed blueprints, **at the tree you are leaving**. A read-only mirror-check seat will now compare the mirror against the Lean statements symbol by symbol; a Stage-B seat will run the doors afterwards. Return the Stage-A envelope now.

## Result envelope (Stage A)
`conclusion` = {"verdict":"mirror-ready|open|already-landed","module_path":"…","theorem_names":[…],"print_axioms":{…},"exit_codes":{"make_lean":n,"make_emit":n,"scribe_corpus_test":n},"public_statements":[{"name":"…","statement":"<full Lean statement text to := by>"}],"mirror_selfcheck":{"parenthesized_only":true|false,"binder_body_symbols":true|false,"nat_div_not_fraction":true|false,"coercions_mirrored":true|false,"relation_in_group_items":false},"proof_shape":{…},"escape_witness":"…","admission_basis":"…","search_trace":[…],"collision_check":"…","fidelity_gate":{…},"assumed_unverified":[…],"open_reasons":[…],"visible_inputs":[…]}, plus `log_ref`.
'''
A=pre.replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)','(STAGE A: module + mirror only — no doors; a mirror-check seat and a Stage-B doors seat follow)')+stepsA+stopA
B_head=pre.split('\n',1)[0].replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)','(STAGE B: doors only — the module, mirror and emitted md are ALREADY in the worktree, uncommitted, and passed a read-only mirror check; run the doors, one builder commit, late dedupe, push, PR)')
B_intro=f'''

You are the Stage-B `implementation_worker` (codex-cli). Worktree `{wt}` on branch `{branch}` already contains the UNCOMMITTED, mirror-checked `{module}.lean`, `Blueprint/{module}.scribe.cs` and emitted `Blueprint/{module}.md` (`git status --porcelain` shows them). Do NOT rewrite the mathematics or the mirror except for the exact fixes listed under "## Mirror-check fixes" below (if that section is empty, touch nothing). Re-run `make lean` (EXIT=0) and `make emit` (EXIT=0) once to confirm the tree, then execute the doors below exactly. Follow `skills/codex-formalize/SKILL.md` Steps 7–8 and `CLAUDE.md` 5⁗. Judge by bare exit codes. Return exactly one result envelope (the original contract, appended).

## Emission order around the door — read this before you touch anything

Stage A left the tree in **Phase A shape**: the module, the mirror **without** any `OpenProblemResolutionClaim`
node, the emitted `.md`, and the `Library/` note if the lane cites literature. Keep it that way through the door.

- **Phase A (before the freeze).** With no claim node and no `Problems/` dossier in the tree: `make lean` EXIT=0,
  `make lean-report` EXIT=0, `make emit` twice with the second reporting 0 changed blueprints, then commit the
  source, then — **in the same command as the door** — verify `git merge-base --is-ancestor origin/dev HEAD`,
  run the late dedupe, and run the deposit. A stop at the ancestry check writes no frozen state
  (`frozen_state_written: false`, zero `Golden/Frozen` changes) and is a CONTINUATION at the next attempt, not a
  lane redo.
- **Phase B (after the freeze).** Now add the `OpenProblemResolutionClaim` node to the Scribe and write the
  `Problems/` dossier whose motivation GID names the now-frozen declaration. `make emit` twice again, second run
  0 changed. Then ONE builder commit carrying the door's delta — the Freeze event, the state pin, the new
  dossier and the re-emitted mirror — followed by `make preflight`, push and `make pr-open`.

Two commits, in that order. If you find yourself wanting to emit the claim before the deposit, re-read this: the
validator is asking for a frozen host, and only the door can give it one.

## Mirror-check fixes
<<MIRROR_FIXES>>



**Render check after ANY Stage-B mirror change (zaremba v3 lesson, 2026-09-05):** if you add or edit Describe nodes here, then after `make emit` run `grep -n -E '&&|\\|\\||==|!=|\\bdecide\\b.*&&' Blueprint/<module>.md` (must be empty — Lean Boolean `&&`/`||`/`==` must be rendered as `∧`/`∨`/`=` inside `Parenthesized`), re-read every new formula, and run `make preflight`: a line `markdown red <your module>.md:…` (KaTeX parse error) or any check naming your module is a STOP-and-fix condition BEFORE `make deposit`; unrelated locale/observe noise is not. '''
gm=re.search(r'## GoalArtifact.*?(?=\n## |\Z)',pre,re.S); goal=gm.group(0)+'\n\n' if gm else ''
base=(here/'templates'/'impl-base-brief.md').read_text()
extra=''.join(re.findall(r'\n6[′″]\. \*\*.*?(?=\n[0-9]+[′″]?\. |\n## )',base,re.S))
stepsB=stepsB.replace('\n7. `git push',extra+'\n7. `git push',1) if '6′.' not in stepsB else stepsB
layout=''
if nyx:
    other='quality' if nyx=='architecture' else 'architecture'
    layout=f"""
## Round-1 review layout (drawn by the orchestrator before this dispatch — write it into the PR body)

The first-published standing table lists the CURRENT round's seats and carriers as a fact: `{nyx} nyxid-oracle /
ChatGPT Pro, {other} codex-cli, tests codex-cli`, at the delivered head, with a zero tally, `Carried-forward
approvals: none.` and `Disagreement adjudication: none.` Do not write "not established"; the assignment is this one.

"""
B=B_head+B_intro+goal+layout+stepsB+env
(sp/'briefs'/f'impl-op-w1-{lane}.stageA.md').write_text(A); (sp/'briefs'/f'impl-op-w1-{lane}.stageB.md').write_text(B)
mc=(here/'templates'/'mirror-check-template.md').read_text().replace('__LANE__',lane).replace('__WORKTREE__',wt).replace('__BRANCH__',branch).replace('__MODULE__',module)
assert '__' not in mc.replace('__init__','')
(sp/'briefs'/f'mirror-check-{lane}.md').write_text(mc)
print('stageA',len(A),'stageB',len(B),'mirror-check',len(mc))
