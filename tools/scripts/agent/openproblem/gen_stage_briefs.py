#!/usr/bin/env python3
"""Split an implementation brief into Stage A (module + mirror + make lean/emit, STOP before any door) and
Stage B (doors: deposit/cover, one builder commit, late dedupe, push, PR). Also fills the mirror-check brief.
usage: gen_stage_briefs.py SCRATCHPAD LANE WORKTREE BRANCH MODULE_RELPATH(no ext, e.g. D5/S1/X/Y)
writes briefs/impl-op-w1-<lane>.stageA.md, .stageB.md, mirror-check-<lane>.md"""
import sys,pathlib,re
sp=pathlib.Path(sys.argv[1]); lane,wt,branch,module=sys.argv[2:6]
src=sp/'briefs'/f'impl-op-w1-{lane}.md'; t=src.read_text()
i=t.index('## Steps'); j=t.index('## Result envelope')
pre,steps,env=t[:i],t[i:j],t[j:]
# split steps: everything up to and including step 4 → stage A; step 5.. → stage B
m=re.search(r'\n5\. \*\*Deposit / cover\*\*',steps); assert m, 'step 5 anchor not found'
stepsA=steps[:m.start()]; stepsB='## Steps (Stage B — doors)\n'+steps[m.start()+1:]
stepsB=stepsB.replace('\n6. ONE builder commit','\n5′. **Anchor cover (mandatory):** `make deposit` freezes the anchor theorem but does NOT write the anchor atom\'s own coverage edge — run `make cover ATOM_ID=<anchor atom> GID=<anchor GID> BASE=origin/dev` after the deposit and verify every target atom (anchor included) is `absorbed-closed` before committing (`ls Meta/Digestion/backfill/<source>/absorbed-closed/ | grep -c <id>`); a lane whose anchor stays residual-open is incomplete (#5480, #5504 needed orchestrator repairs).\n6. ONE builder commit',1)
stopA='''
4′. **STOP HERE (Stage A ends before any freeze).** Do NOT run `make deposit`, `make cover`, `git commit`, `git push` or `make pr-open`. Leave the new `.lean`, `.scribe.cs` and the emitted `.md` as UNCOMMITTED files in the worktree (`git status --porcelain` must list exactly those three new files plus nothing else tracked-modified). A read-only mirror-check seat will now compare the mirror against the Lean statements symbol by symbol; a Stage-B seat will run the doors afterwards. Return the Stage-A envelope now.

## Result envelope (Stage A)
`conclusion` = {"verdict":"mirror-ready|open|already-landed","module_path":"…","theorem_names":[…],"print_axioms":{…},"exit_codes":{"make_lean":n,"make_emit":n,"scribe_corpus_test":n},"public_statements":[{"name":"…","statement":"<full Lean statement text to := by>"}],"mirror_selfcheck":{"parenthesized_only":true|false,"binder_body_symbols":true|false,"nat_div_not_fraction":true|false,"coercions_mirrored":true|false,"relation_in_group_items":false},"proof_shape":{…},"escape_witness":"…","admission_basis":"…","search_trace":[…],"collision_check":"…","fidelity_gate":{…},"assumed_unverified":[…],"open_reasons":[…],"visible_inputs":[…]}, plus `log_ref`.
'''
A=pre.replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)','(STAGE A: module + mirror only — no doors; a mirror-check seat and a Stage-B doors seat follow)')+stepsA+stopA
B_head=pre.split('\n',1)[0].replace('(probe-verified; same-PR deposit + cover; open the PR, no auto-merge)','(STAGE B: doors only — the module, mirror and emitted md are ALREADY in the worktree, uncommitted, and passed a read-only mirror check; run the doors, one builder commit, late dedupe, push, PR)')
B_intro=f'''

You are the Stage-B `implementation_worker` (codex-cli). Worktree `{wt}` on branch `{branch}` already contains the UNCOMMITTED, mirror-checked `{module}.lean`, `Blueprint/{module}.scribe.cs` and emitted `Blueprint/{module}.md` (`git status --porcelain` shows them). Do NOT rewrite the mathematics or the mirror except for the exact fixes listed under "## Mirror-check fixes" below (if that section is empty, touch nothing). Re-run `make lean` (EXIT=0) and `make emit` (EXIT=0) once to confirm the tree, then execute the doors below exactly. Follow `skills/codex-formalize/SKILL.md` Steps 7–8 and `CLAUDE.md` 5⁗. Judge by bare exit codes. Return exactly one result envelope (the original contract, appended).

## Mirror-check fixes
<<MIRROR_FIXES>>



**Render check after ANY Stage-B mirror change (zaremba v3 lesson, 2026-09-05):** if you add or edit Describe nodes here, then after `make emit` run `grep -n -E '&&|\\|\\||==|!=|\\bdecide\\b.*&&' Blueprint/<module>.md` (must be empty — Lean Boolean `&&`/`||`/`==` must be rendered as `∧`/`∨`/`=` inside `Parenthesized`), re-read every new formula, and run `make preflight`: a line `markdown red <your module>.md:…` (KaTeX parse error) or any check naming your module is a STOP-and-fix condition BEFORE `make deposit`; unrelated locale/observe noise is not. '''
gm=re.search(r'## GoalArtifact.*?(?=\n## |\Z)',pre,re.S); goal=gm.group(0)+'\n\n' if gm else ''
base=(sp/'briefs'/'impl-op-w1-ppn.md').read_text()
extra=''.join(re.findall(r'\n6[′″]\. \*\*.*?(?=\n[0-9]+[′″]?\. |\n## )',base,re.S))
stepsB=stepsB.replace('\n7. `git push',extra+'\n7. `git push',1) if '6′.' not in stepsB else stepsB
B=B_head+B_intro+goal+stepsB+env
(sp/'briefs'/f'impl-op-w1-{lane}.stageA.md').write_text(A); (sp/'briefs'/f'impl-op-w1-{lane}.stageB.md').write_text(B)
mc=(sp/'briefs'/'mirror-check-template.md').read_text().replace('__LANE__',lane).replace('__WORKTREE__',wt).replace('__BRANCH__',branch).replace('__MODULE__',module)
assert '__' not in mc.replace('__init__','')
(sp/'briefs'/f'mirror-check-{lane}.md').write_text(mc)
print('stageA',len(A),'stageB',len(B),'mirror-check',len(mc))
