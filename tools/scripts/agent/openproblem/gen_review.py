#!/usr/bin/env python3
"""Generate the three review-triplet briefs for one PR from briefs/review-template.md.
usage: gen_review.py LANE PR BRANCH WORKTREE IMPL_ENVELOPE TARGET_FILE NYXID_SEAT
  LANE          short lane name (zeck|axis|parity|rouche…)
  PR            PR number
  BRANCH        head branch
  WORKTREE      local worktree with the branch checked out
  IMPL_ENVELOPE path to the implementation seat's result.json (or 'none')
  TARGET_FILE   text file describing the authoritative target (atom ids + statements)
  NYXID_SEAT    architecture|quality (from the recorded draw; tests is always codex)
Writes briefs/review-<LANE>-<role>.md for architecture, quality, tests; the nyxid seat gets a compact URL-based variant (<40KB).
"""
import sys, subprocess, pathlib, re
sp = pathlib.Path(__file__).resolve().parent
lane, pr, branch, worktree, impl_env, target_file, nyx_seat = sys.argv[1:8]
tpl = (sp/'briefs'/'review-template.md').read_text()
ga = (sp/'goal-artifact.yaml').read_text().rstrip()
head = subprocess.check_output(['git','-C',worktree,'rev-parse','HEAD'],text=True).strip()
files = subprocess.check_output(['git','-C',worktree,'diff','--name-status','origin/dev...HEAD'],text=True).strip()
title = subprocess.check_output(['gh','pr','view',pr,'-R','the-omega-institute/trureturing','--json','title','--jq','.title'],text=True).strip()
target = pathlib.Path(target_file).read_text().strip()
biases = {
 'architecture': 'boundaries, contracts, coupling, maintainability: module placement (natural owner bucket, capacity read from the owner file), import minimality (every import consumed; no false ledger edge), namespace/GID = path, generality tag vs weakest import, Blueprint mirror shape and formula DSL (visible grouping MUST be `Parenthesized` — `Grp` emits TeX braces that print no parentheses; no relation node inside `LatexGroup.Items`, an uncovered corpus shape that turns CI red), no second source of truth (def-level duplicate search on FRESH current dev after `git fetch origin` — fleet lanes land owners within hours, cf. #5423), freeze-event prerequisites = actual imports; 5⁗ escape witness on the LIVE proof path.',
 'quality': 'fidelity/non-hollowness: statements byte-faithful to the obligation atoms (echo table; `make show-atom` is authority); DEFINITION fidelity: every object the atom DEFINES by a formula (a kernel, an energy, a count, a predicate) must appear in Lean either as that literal defining expression or with a PUBLIC identity theorem equating the Lean definition to the atom expression, and the covered statement must refer to the atom-defined object — a mathematically equivalent replacement definition without an addressable public identity is a fidelity FAIL (cf. #5510 paired-mode vs signed-mode Fejér kernel); no weakening/strengthening/added hypotheses; conclusion not True/tautology; both sides of every equation independently anchored; read the EMITTED `.md` value by value — every rendered parenthesis/grouping must match the atom (a `Grp`-rendered `n·(xy+xz+yz)` reads `nxy+xz+yz`); no private helper restating a frozen theorem; proof_shape/escape_witness/admission_basis per public theorem audited against the elaborated proof; companions have honest directed edges; PR body readings (exit codes, HEAD, #print axioms) and provenance triple present.',
 'tests': 'verification strength: RUN `make lean` (or scoped `lake build <module>`) and `make emit` in the worktree at HEAD and report exit codes; `#print axioms` for every public theorem (std3 only); `git fetch origin` FIRST, then re-run the def/theorem duplicate greps and conclusion-shape searches on the FRESH origin/dev (a frozen owner landed by another driver after the seat started is a blocking bind-first defect, cf. #5423); run the Scribe `FormulaCorpusInventoryTests` and `DocumentDiscoveryTests` and report exit codes; verify every covered atom (INCLUDING the atom of the deposit anchor itself) moved to absorbed-closed and that deposit+covers sit in ONE builder commit; verify the Freeze event and ledger moves are door output only (no hand edits under Meta/Digestion or Golden/Frozen); Scribe test subset for the document; mutation sanity (does deleting the claimed escape witness break the main theorem? — reason from the proof term, do not edit tracked files).',
}
for role in ['architecture','quality','tests']:
    t = tpl.replace('__ROLE__', role).replace('__PR__', pr).replace('__TITLE__', title).replace('__GOAL_ARTIFACT__', ga)
    t = t.replace('__BRANCH__', branch).replace('__HEAD__', head).replace('__TARGET__', target).replace('__IMPL_ENVELOPE__', impl_env).replace('__FILES__', '\n' + files).replace('__BIAS__', biases[role])
    if role == nyx_seat:
        t = t.replace('__WORKTREE__', 'n/a for this carrier — read the PR diff at https://github.com/the-omega-institute/trureturing/pull/' + pr + '/files and the raw files at https://raw.githubusercontent.com/the-omega-institute/trureturing/' + head + '/<path>; local paths are unreadable references')
        t = t.replace('Return exactly one result envelope (shape at the end / contract appended).', 'Return EXACTLY one JSON object inside a single ```json fence and nothing else (shape at the end); keep the reply under 12,000 characters.')
    else:
        t = t.replace('__WORKTREE__', worktree)
    assert '__' not in t.replace('__init__',''), (role, re.findall(r'__[A-Z_]+__', t)[:5])
    out = sp/'briefs'/f'review-{lane}-{role}.md'
    out.write_text(t); print('wrote', out.name, len(t.encode()), 'bytes')
