/- GID: D5/S1/Recurrence/CarryCancellation
   generality: G
   mirror-B: D5/B/S1/Recurrence/CarryCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A recurrence makes a consecutive block and its carry digit equal in weight. -/

import Mathlib.Data.Finsupp.Weight

/- Provenance: pinned Mathlib supplies `Finsupp.weight`,
   `Finsupp.weight_single`, and finite-sum additivity. Its Fibonacci library
   supplies `Nat.fib_add_two`, but no fixed-width carry theorem or
   Tribonacci recurrence declaration was found. -/

namespace D5.S1.Recurrence.CarryCancellation

open scoped BigOperators

/-- A finite digit state records a natural multiplicity at each position. -/
abbrev DigitState := ℕ →₀ ℕ

/-- One occupied digit at every position from `start` through
`start + width - 1`. -/
noncomputable def consecutiveBlock (width start : ℕ) : DigitState :=
  ∑ i ∈ Finset.range width, Finsupp.single (start + i) 1

/-- The single digit produced by carrying a consecutive block. -/
noncomputable def carryDigit (width start : ℕ) : DigitState :=
  Finsupp.single (start + width) 1

/-- Evaluate a finite digit state against an arbitrary additive weight
sequence. -/
noncomputable def weightedValue {M : Type*} [AddCommMonoid M]
    (weights : ℕ → M) : DigitState →+ M :=
  Finsupp.weight weights

/-- If the weight at `start + width` is the sum of the preceding `width`
weights, replacing that consecutive block by its carry digit preserves total
weight. The untouched state `rest` is arbitrary, so this is a local rewrite
inside any finite digit state. -/
theorem recurrence_carry_preserves_weight {M : Type*} [AddCommMonoid M]
    (weights : ℕ → M) (rest : DigitState) (width start : ℕ)
    (recurrence : weights (start + width) =
      ∑ i ∈ Finset.range width, weights (start + i)) :
    weightedValue weights (rest + consecutiveBlock width start) =
      weightedValue weights (rest + carryDigit width start) := by
  classical
  simp only [map_add, weightedValue, consecutiveBlock, map_sum,
    Finsupp.weight_single, one_nsmul, carryDigit]
  rw [recurrence]

end D5.S1.Recurrence.CarryCancellation
