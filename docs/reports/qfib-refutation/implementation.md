# Conjecture 5.4 necessity refutation: implementation record

Skill context: `lean4`; Codex implementation worker, single implementation source,
no independent reviewer in this worker. The user supplied the candidate; this worker
independently checks the source, arithmetic, formalization and build.

## Preregistered target

Tier 1, arXiv:2605.12822v1, Conjecture 5.4, **necessity only**. The proposed
closed `claim` quantifies over all natural r, k, positive entries and b, assumes
r ≥ 2, k ≥ 1, and (k ≤ 3 OR r ≤ 3), and says unimodality implies
(some r ∣ aᵢ OR b ≤ 1 + Σ aᵢ/r). The proposed closed `result` has type `¬ claim`.
The source and literature status remain unverified at this checkpoint.

Proposed escape witness: the exact polynomial (1+q)^6(1+q^3) is unimodal,
while its parameters violate both alternatives of the stated condition.
This new numerical fact is to be used on the live path of the refutation;
positive finite instances will not be exposed as separate public theorems.
Proposed admission basis: `escape-witness`; computational use: `certified-instance`
with `refutes=gid:<claim>`, typed `claim` and `result` (spec A5.1).

Controls, before computation: k=1,2,3,4,5 must be non-unimodal; k=6,7,9 must
be unimodal. k=6 is the selected witness. No claim of a general k ≥ 6 theorem.

Success: kernel refutation, requested make/Scribe gates, no prohibited proof
devices, and PR opened. Reversal: the source or computation invalidates the
candidate. Blocked: actual Lean attempt with its exact remaining goal/error.
No theory volume, ingest, atom creation, or coverage backfill is planned.

## Workspace and first search

Base: `248a800843acf89ed184074d66a8d577fc028f99`.
Worktree: `/Users/chronoai/trureturing-qfib-unimodal`.
Branch: `lane/math/qfib-unimodal`; initially clean and based on origin/dev.
Read the complete CLAUDE.md, agents/CONTEXT.md, Lean skill and spec A5.1.

Ordered search step 1: `rg -n -i 'fibonomial|unimodal|q.?analog|log.?concav'
D5 Problems` found BoundedTimeSlice, DebSokalConjectureFourRefutation,
KarpQuadraticTruncations, and an unrelated Vatter problem. Their public APIs
are being examined; keyword hits alone are not a semantic non-reuse verdict.
`D5/S0/Certificates` has 36 files (recursive `find ... -type f | wc -l`).
The registered Certificates domain is S0 and includes kernel refutation certificates.
The existing DebSokal module confirms the seven-line `refutes=gid` header syntax.
`make help` exposes `deposit-uncovered`, the canonical no-atom entry point.

## Unclaimed

No sufficiency result, no universal family classification, no global minimality
among all parameter tuples, no exhaustive world-literature priority claim, no
independent review or successful build is claimed at this checkpoint.
