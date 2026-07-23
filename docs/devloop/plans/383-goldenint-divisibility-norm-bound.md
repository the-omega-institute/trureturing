# Plan #383: GoldenInt Divisibility Norm Bound

## GOAL

Converge #383 to one implementable objective: add and mirror a public theorem
`D5.S0.Carrier.norm_natAbs_le_of_dvd` proving that for `x y : GoldenInt`,
`y ≠ 0` and `x ∣ y` imply `(norm x).natAbs ≤ (norm y).natAbs`.

This plan PR must not implement the Lean theorem or the Blueprint mirror. It is
only the planning artifact for the later implementation slot.

## Grounding

- Origin #383 asks for one genuinely new, nontrivial, worthwhile `GoldenInt`
  theorem using only the already closed `D5/S0/Carrier/` library, plus
  Blueprint narrative.
- `D5/S0/Carrier/Norm.lean:12-19` defines `norm` and proves the base values
  `norm_zero`, `norm_one`, and `norm_phi`.
- `D5/S0/Carrier/Norm.lean:34-45` proves `norm_mul` and packages
  `normMonoidHom`.
- `D5/S0/Carrier/Euclidean.lean:14-29` proves `norm_eq_zero_iff`.
- `D5/S0/Carrier/Euclidean.lean:155-165` installs
  `EuclideanDomain GoldenInt`.
- `D5/S0/Carrier/Euclidean.lean:146-150` contains the private
  multiplication-side norm bound `norm_le_norm_mul_right`.
- Local search found no existing `D5/S0/Carrier/Divisibility` module and no
  public theorem named `norm_natAbs_le_of_dvd`.

## Approach

Use the standard normed-domain divisibility argument, which is the established
algebraic practice for exposing a divisor bound from a multiplicative norm:
destructure `x ∣ y` as `y = x * z`, rewrite by `norm_mul` and
`Int.natAbs_mul`, use `y ≠ 0` plus `norm_eq_zero_iff` to rule out the zero-norm
case, then apply the natural-number divisor/order lemma. The later Lean proof
should first try the existing general lemma `EuclideanDomain.val_dvd_le`; if it
does not fit the custom `norm` spelling directly, use the direct proof above.

Place the later Lean theorem in a new derived S0 Carrier module, likely
`D5/S0/Carrier/Divisibility.lean`, with `generality: I`, importing
`D5.S0.Carrier.Euclidean`. Add the mirror as
`Blueprint/D5/S0/Carrier/Divisibility.scribe.cs` and emitted markdown, using
`DescribeStatement.FromLean` and repo-derived provenance unless literature
search in that implementation slot justifies a library note. Remember the
explicit import surface in `Trureturing.lean` when adding the new Lean module.

## Implementation Acceptance

- Future implementation adds one real Lean theorem, not a placeholder and not a
  vacuous statement.
- `lake build` succeeds.
- `#print axioms D5.S0.Carrier.norm_natAbs_le_of_dvd` shows no `sorryAx` and no
  custom or non-mathlib axiom.
- Future Blueprint narrative mirrors the exact Lean theorem, and
  `make emit-check` succeeds after emission.
- Future implementation keeps the change conservative: append the new node and
  necessary imports and emissions only; do not edit frozen theorem statements.

## Non-Goals

Do not implement PID, UFD, irreducible or prime norm classification, full
factorization, unit classification changes, new harness behavior, or devloop
workflow changes. Do not ask this plan PR to duplicate consensus, CI, review, or
merge gates.
