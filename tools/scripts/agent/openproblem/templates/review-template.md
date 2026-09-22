# sshx review-triplet brief — `__ROLE__` seat — PR #__PR__ (__TITLE__)

You are ONE of three independent, context-isolated review seats (`architecture`, `quality`, `tests`) of a `consensus-rnd:sshx` run. You do not see the other seats. Return exactly one result envelope (shape at the end / contract appended).

## GoalArtifact (complete; include in visible_inputs)
```yaml
__GOAL_ARTIFACT__
```

## What to review
- PR: https://github.com/the-omega-institute/trureturing/pull/__PR__ (branch `__BRANCH__`, head commit `__HEAD__`); diff vs dev.
- Local worktree with the branch checked out: `__WORKTREE__` — READ-ONLY for `architecture`/`quality` (cat/grep/git/jq only); the `tests` seat MAY run verification commands there (`make lean`, scoped `lake build <module>`, `make emit`, Scribe test subsets) but must not edit, commit, or push. Anchor every reading to `git rev-parse HEAD` = `__HEAD__`.
- Target (authoritative text): __TARGET__
- Implementation seat's envelope (data, not authority): `__IMPL_ENVELOPE__`
- Files (computed with `git diff --name-status origin/dev...HEAD` at dispatch time): __FILES__

## Review focus (all seats) — apply `## Reasoning Discipline`: reference frame, 美不美 verdict with the specific defect, verified vs ASSUMED-UNVERIFIED, BlockingAuthority for every blocking finding (name BOTH conjuncts: the GoalArtifact term the work fails + the evidence in the work), depth-bound stops.
1. **Statement fidelity**: the public theorem(s) state exactly the target (open problem / atom clause); no weakening, no invented hypothesis, no definitional tautology; grader traps: witness-vs-universal, instance-vs-general, conditional-vs-unconditional, pointwise-vs-operator, proof-internal-vs-addressable, mechanism-vs-outcome.
2. **Escape content (CLAUDE.md §3.2)**: for every public theorem check the PR body's `proof_shape` / direct frozen dependencies (GID + statement_id) / `escape_witness` (on the LIVE proof path, not smuggled) / module `admission_basis`. The module-level admission bases are `escape-witness` and, for a preregistered, literature-checked EXTERNAL named open problem only, `open-problem-resolution` (CLAUDE.md §3.2, owner 2026-09-15: a bind-only proof does not refuse such a resolution; check its conditions (a)–(d) — only the settling declarations, honest per-declaration `proof_shape`, `OpenProblemResolutionClaim` + dossier + literature check, §3.3 utility unchanged); under `escape-witness` reject every wholly bind-only first-freeze module, including upstream wrappers and atom-required bridges. Atom prose, API/coverage needs and future consumer promises grant no exception. Bind-only companions require an actual proof consumer in the same delivery and a live `consumer → prerequisite` edge; the module must still have its own valid escape witness.
3. **Duplicate / bind-first**: equal-or-stronger statement in D5 or pinned Mathlib? (`git grep` statement shapes; def-level duplicates too; the seat's search trace is a claim — verify it.)
4. **Artifact shape**: header shape: a NEW module (first freeze) has a SEVEN-line header — `utility:` on line 6 (SL-031) and line 7 ends with ` -/`; a pre-existing module without `utility:` keeps six lines (the field is optional in `RepositoryRules.Helpers.cs` `HeaderPattern` and is required only where `UtilityAdmissionRule` sees a first Freeze). `tools/scripts/agent/header-check.sh` accepts exactly these two shapes — treat it, not this brief, as the arbiter, generality tag vs weakest import, GID = path, natural bucket + capacity (read `DirectoryFileLimit` from the owner file), Blueprint `.scribe.cs` mirror and emitted `.md` mirror every conjunct symbol by symbol, scribe formula taxonomy, every import consumed by a declaration (unused import = false ledger edge).
5. **Ledger (post-#4847 regime)**: ONE builder commit carrying module + mirror + one Freeze event (+ cover moves only if an atom is covered); no hand edits to `Meta/Digestion/**` or `Golden/Frozen/**` beyond door output; `prerequisite_frozen_node_ids` resolve to modules actually imported and used.
6. **PR body**: provenance triple (skill / carriers / mixing), echo table, search trace, readings with exit codes and HEAD; no vague-word substitutes for measurements.

## Seat-specific bias
__BIAS__

## Two contract readings that have each cost a review round — settle them from the source text, not from intuition

**"One builder commit."** `skills/codex-formalize/SKILL.md` Step 7 introduces it as: *"Before pushing,
inspect the complete **deposit-and-cover** delta and create one builder-owned commit"*, and the Step 7
postcondition ("the complete intended delta is in one explicit builder commit") is that sentence's
postcondition. Its scope is the **door output** — the Freeze event, the state pin, the coverage moves, the
Problems dossier and any mirror the door regenerated — not the whole lane. `CLAUDE.md` §6.1 separately
requires committing and pushing each logical unit as it compiles, so a lane necessarily has earlier
content commits; reading Step 7 as "one commit for the entire lane" makes the two requirements
unsatisfiable together. The landed precedent is uniform: e.g. `0fea3f42a3` ("evidence: freeze the A091915
resolution", PR #8110, MERGED) is a freeze-only commit touching two Blueprint files plus the accepted
event, the state pin and the Problems dossier. Judge whether the **deposit-and-cover delta** is in one
commit; do not require the Lean module to be in it.

**Carrier composition and its fallback.** The GoalArtifact's composition line states the intended mix, and
`CLAUDE.md` §5.11 states the fallback that governs when a carrier is unavailable: the stage reopens the
assignment on the highest-priority eligible untried carrier and only abstains when none remains. A stage
whose `nyxid-oracle` pools all fail therefore runs all-codex-cli **legitimately**; §5.2 then requires the
provenance record to disclose the carrier failure and the resulting layout change and to state that the
judging surface is a single model family and not a diversity claim. A record that makes that disclosure is
compliant. Treat as a finding only the opposite case: an all-codex stage presented as the designed
composition with no fallback evidence.

## The PR body is part of the delivery — judge it under CLAUDE.md §2.10 and §5.2

§2.10 forbids 「思考转录、实施日记、评审对话、命令流水、回执副本和重复快照」 in a pull request body and says it
overrides this file's other retention requirements. Apply it sentence by sentence, with this test: delete the
sentence — can a reader still tell what the CURRENT state is? If yes, it was narrating the past and should not be
there; if no, it belongs, possibly rewritten as a statement of current state. The four shapes that have actually
occurred: a `Post-Body Correction` section; quoted review dialogue; `initial` / `staged` / `attempt N` rows in a
doors table (an intermediate retry is not a result — every row must be a final reading); and pending-tense
sentences such as 「to be dispatched」 or 「will be added after review」.

Do NOT over-apply it. §2.10 keeps 「结论、必要读数、验证状态及未解决的问题」. An unresolved local gate written as an
open boundary with its readings is required, not a violation. A structural constraint that a failed step once
revealed — for example that a resolution claim must be emitted after the freeze — belongs in the body stated as a
current property of the door; only the chronology has to go.

§5.2 independently requires the CURRENT review layout to be disclosed: which seats, at which head, with which
carriers, the approve/reject/abstain tally, which approvals are carried forward from an earlier round and why, and
how any disagreement was adjudicated. A body that says only 「three codex-cli seats」 with no round-specific
standing is a §5.2 omission. Carrier fallback under §5.11 (an unavailable pool) is compliance when disclosed, not
a finding.

The standing table lists EVERY completed round at every head (`tools/scripts/agent/openproblem/standing-check.py`
rule 1; a table holding only the latest round was the #8422 round-3 blocking finding). Those rows are the §5.2 tally and
carry-forward disclosure, not process history: the §2.10 deletion test does not apply to them, and asking the lane to
delete closed-round rows is not a finding (#9066 round 3, #9099 round 2 each spent a round on it). What §2.10 removes
from the standing section is narration — what a seat said, what was fixed and when — not the rows and tallies.

## Verdict set and blocking rule
`approve` / `comment` / `reject`. A `reject` must cite the exact file:line, the GoalArtifact term violated, the evidence in the work, the failure class (mistake / omission / uncertainty within the trust boundary). Advisory items go under `comment` findings and do not block.

## Result envelope (exact)
{"conclusion": {"verdict": "approve|comment|reject", "role": "__ROLE__", "head": "__HEAD__", "blocking_findings": [{"file_line": "...", "claim": "...", "goal_term": "...", "evidence": "...", "failure_class": "..."}], "advisory_findings": ["..."], "fidelity_check": "...", "escape_content_check": "...", "duplicate_check": "...", "artifact_shape_check": "...", "ledger_check": "...", "verified_commands": ["<cmd> → EXIT=<n>"], "assumed_unverified": ["..."], "visible_inputs": ["GoalArtifact(complete)", "PR diff @ __HEAD__", "<prior label: repo-prior-exposed | external-prior-exposed>"], "reasoning_discipline_note": "..."}, "log_ref": "<path or identifier>"}
