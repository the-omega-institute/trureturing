# Plan #401: GoldenInt Norm Powers

## GOAL

Converge #401 to one implementable objective: add and mirror a public theorem
`D5.S0.Carrier.norm_pow` proving that for every `x : GoldenInt` and `n : Nat`,
`norm (x ^ n) = norm x ^ n`.

This plan PR must not implement the Lean theorem, Blueprint mirror, generated
Markdown, imports, or tests. It is only the planning artifact for the later
implementation slot.

## Grounding

- Origin #401 asks for one genuinely new, non-vacuous, worthwhile `GoldenInt`
  theorem using only the already closed `D5/S0/Carrier/` library, plus a
  Blueprint narrative; the request marker is
  `theory-selfgrowth:frontier-request:v1:loning`.
- `D5/S0/Carrier/Norm.lean:12-19` defines `norm` and its base values.
- `D5/S0/Carrier/Norm.lean:34-45` proves `norm_mul` and packages the
  multiplicative norm as `normMonoidHom`, which is the direct proof spine for
  powers.
- `D5/S0/Carrier/Units.lean:53-55` proves only the special case
  `norm_phi_pow`; the general `GoldenInt` power law is not present.
- Local search found no existing public theorem named
  `D5.S0.Carrier.norm_pow` and no general `norm (x ^ n) = norm x ^ n` theorem
  in `D5`, `Blueprint`, or `docs/devloop/plans`.
- `docs/devloop/plans/383-goldenint-divisibility-norm-bound.md:5-7` already
  reserves the divisibility norm-bound goal, and the board snapshot shows #400
  implementing #383, so this plan deliberately avoids that active lane.
- `Blueprint/D5/S0/Carrier/Norm.scribe.cs:30-45` shows the current Scribe
  pattern for adding a Lean-backed theorem to the norm narrative with
  `DescribeStatement.FromLean` and a LaTeX statement.
- `docs/develop/spec/golden-ledger-repo-spec.md:139` makes typed Scribe
  `DocumentBlock.Describe` the canonical Blueprint source, and `Makefile:22` /
  `Makefile:38` expose `lake build` and `emit-check` as the verification
  commands.

## Approach

Use the established algebraic best practice for multiplicative invariants:
expose the power law through the already packaged monoid homomorphism, not by
redoing coordinate induction or duplicating polynomial arithmetic. The later
Lean proof should be the direct `normMonoidHom.map_pow x n` consequence,
keeping the statement exact and without magic constants, proxy checks, or
symptom branches.

Place the later Lean theorem in a new derived S0 Carrier module, likely
`D5/S0/Carrier/NormPowers.lean`, with `generality: I`, importing only
`D5.S0.Carrier.Norm` unless Lean requires a narrower mathlib import already
available through that module. Add the root import in `Trureturing.lean` only as
needed for the new module to participate in the full build.

Mirror the theorem in `Blueprint/D5/S0/Carrier/NormPowers.scribe.cs` and emitted
Markdown using
`DescribeStatement.FromLean(LeanTheorem("D5/S0/Carrier/NormPowers.norm_pow"))`,
`DescribeProvenance.RepoDerived()`, and a LaTeX statement equivalent to the Lean
declaration.

## Implementation Acceptance

- Future implementation adds one real public Lean theorem
  `D5.S0.Carrier.norm_pow (x : GoldenInt) (n : Nat) :
  norm (x ^ n) = norm x ^ n`, not a placeholder and not a vacuous statement.
- Future implementation adds Lean echo checks before or with the proof, for
  example one checked specialization recovering `norm_phi_pow` from
  `norm_pow phi n` and one checked square case for arbitrary `x`; these checks
  must compile under `lake build`.
- `lake build` succeeds.
- `#print axioms D5.S0.Carrier.norm_pow` shows no `sorryAx` and no custom or
  non-mathlib axiom.
- Future Blueprint narrative mirrors the exact Lean theorem, and
  `make emit-check` succeeds after emission.
- Future implementation is conservative: append the new node and necessary
  imports/emissions only; do not alter existing closed theorem statements.

## Non-Goals

Do not implement the #383 divisibility norm bound, the #398 characteristic
equation, PID, UFD, irreducible or prime norm classification, unit
classification changes, integer-power/zpow laws for arbitrary nonunits,
Euclidean-domain changes, harness changes, workflow changes, or any
novelty/worth scoring. Do not ask this plan PR to duplicate devloop consensus,
CI, PR review, or merge gates.
