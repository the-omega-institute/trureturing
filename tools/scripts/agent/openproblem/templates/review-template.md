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
2. **Escape content (CLAUDE.md 5⁗)**: for every public theorem check the PR body's `proof_shape` / direct frozen dependencies (GID + statement_id) / `escape_witness` (on the LIVE proof path, not smuggled) / module `admission_basis`. A first-freeze module with no admission basis is a reject.
3. **Duplicate / bind-first**: equal-or-stronger statement in D5 or pinned Mathlib? (`git grep` statement shapes; def-level duplicates too; the seat's search trace is a claim — verify it.)
4. **Artifact shape**: six-line header (line 6 ends with ` -/`), generality tag vs weakest import, GID = path, natural bucket + capacity (read `DirectoryFileLimit` from the owner file), Blueprint `.scribe.cs` mirror and emitted `.md` mirror every conjunct symbol by symbol, scribe formula taxonomy, every import consumed by a declaration (unused import = false ledger edge).
5. **Ledger (post-#4847 regime)**: ONE builder commit carrying module + mirror + one Freeze event (+ cover moves only if an atom is covered); no hand edits to `Meta/Digestion/**` or `Golden/Frozen/**` beyond door output; `prerequisite_frozen_node_ids` resolve to modules actually imported and used.
6. **PR body**: provenance triple (skill / carriers / mixing), echo table, search trace, readings with exit codes and HEAD; no vague-word substitutes for measurements.

## Seat-specific bias
__BIAS__

## Verdict set and blocking rule
`approve` / `comment` / `reject`. A `reject` must cite the exact file:line, the GoalArtifact term violated, the evidence in the work, the failure class (mistake / omission / uncertainty within the trust boundary). Advisory items go under `comment` findings and do not block.

## Result envelope (exact)
{"conclusion": {"verdict": "approve|comment|reject", "role": "__ROLE__", "head": "__HEAD__", "blocking_findings": [{"file_line": "...", "claim": "...", "goal_term": "...", "evidence": "...", "failure_class": "..."}], "advisory_findings": ["..."], "fidelity_check": "...", "escape_content_check": "...", "duplicate_check": "...", "artifact_shape_check": "...", "ledger_check": "...", "verified_commands": ["<cmd> → EXIT=<n>"], "assumed_unverified": ["..."], "visible_inputs": ["GoalArtifact(complete)", "PR diff @ __HEAD__", "<prior label: repo-prior-exposed | external-prior-exposed>"], "reasoning_discipline_note": "..."}, "log_ref": "<path or identifier>"}
