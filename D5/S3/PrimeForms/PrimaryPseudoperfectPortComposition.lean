/- GID: D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PrimaryPseudoperfectPortComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coprime quotient derivatives compose primary-pseudoperfect ports exactly. -/

import D5.S3.PrimeForms.PrimaryPseudoperfectPorts

/-!
# Primary pseudoperfect port composition

This module extends the frozen primary-pseudoperfect API with the coprime product rule and its
port calculus.  Natural subtraction causes no loss in the composition law: multiplication
distributes over truncated subtraction, and two successive subtractions equal subtraction of
the corresponding sum.

## Search receipt

Repository searches for `portDelta`, a coprime multiplication theorem for `squarefreeDeriv`, and
the stated primary-pseudoperfect coprime extension found only the source obligations and the
frozen owner imported above.  In pinned Mathlib, `Nat.Coprime.primeFactors_mul`,
`Nat.Coprime.disjoint_primeFactors`, `Nat.mul_div_assoc`, `Nat.sub_mul`, and the natural
subtraction normal forms supply the exact supporting API.  No existing declaration states any of
the three conclusions below.
-/

namespace D5.S3.PrimeForms.PrimaryPseudoperfectPortComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.PrimeForms.PrimaryPseudoperfectPorts

/-- The residual after charging the squarefree derivative of `B` at rate `R` against `c * B`. -/
def portDelta (R c B : Nat) : Nat :=
  c * B - R * squarefreeDeriv B

/-- The quotient sum obeys a Leibniz rule on coprime natural factors. -/
theorem squarefreeDeriv_mul_of_coprime (A B : Nat) (hAB : A.Coprime B) :
    squarefreeDeriv (A * B) =
      A * squarefreeDeriv B + B * squarefreeDeriv A := by
  classical
  rw [squarefreeDeriv, hAB.primeFactors_mul,
    Finset.sum_union hAB.disjoint_primeFactors]
  calc
    (∑ p ∈ A.primeFactors, A * B / p) +
          ∑ p ∈ B.primeFactors, A * B / p =
        (∑ p ∈ A.primeFactors, B * (A / p)) +
          ∑ p ∈ B.primeFactors, A * (B / p) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [mul_comm A B, Nat.mul_div_assoc B (Nat.dvd_of_mem_primeFactors hp)]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Nat.mul_div_assoc A (Nat.dvd_of_mem_primeFactors hp)]
    _ = B * squarefreeDeriv A + A * squarefreeDeriv B := by
      rw [squarefreeDeriv, squarefreeDeriv, Finset.mul_sum, Finset.mul_sum]
    _ = A * squarefreeDeriv B + B * squarefreeDeriv A := by ac_rfl

/-- Coprime multiplication composes ports by first absorbing `A` and then absorbing `B`. -/
theorem portDelta_mul_of_coprime (R c A B : Nat) (hAB : A.Coprime B) :
    portDelta R c (A * B) =
      portDelta (R * A) (portDelta R c A) B := by
  simp only [portDelta, squarefreeDeriv_mul_of_coprime A B hAB,
    Nat.mul_add, Nat.sub_mul, Nat.sub_sub]
  congr 1 <;> ring

/-- A positive unit residual is equivalent to the corresponding untruncated balance equation. -/
private theorem portDelta_eq_one_iff (R C : Nat) :
    portDelta R 1 C = 1 ↔ C = 1 + R * squarefreeDeriv C := by
  simp only [portDelta, one_mul]
  omega

/-- A coprime squarefree factor extends a primary pseudoperfect number exactly when its port
residual is one. -/
theorem isPPN_mul_squarefree_coprime_iff_portDelta_eq_one
    (K C : Nat) (hK : IsPPN K) (hC : Squarefree C) (hCgt : 1 < C)
    (hKC : K.Coprime C) :
    IsPPN (K * C) ↔ C - K * squarefreeDeriv C = 1 := by
  have hSquarefree : Squarefree (K * C) :=
    (Nat.squarefree_mul hKC).2 ⟨hK.1, hC⟩
  have hLarge : 1 < K * C := by
    nlinarith [hK.2.1, hCgt]
  have hDeltaBalance :
      C - K * squarefreeDeriv C = 1 ↔
        C = 1 + K * squarefreeDeriv C := by
    simpa only [portDelta, one_mul] using portDelta_eq_one_iff K C
  constructor
  · intro hProduct
    apply hDeltaBalance.2
    have hProductEquation := hProduct.2.2
    rw [squarefreeDeriv_mul_of_coprime K C hKC] at hProductEquation
    nlinarith [hK.2.2, hProductEquation]
  · intro hDelta
    refine ⟨hSquarefree, hLarge, ?_⟩
    rw [squarefreeDeriv_mul_of_coprime K C hKC]
    nlinarith [hK.2.2, hDeltaBalance.1 hDelta]

#print axioms squarefreeDeriv_mul_of_coprime
#print axioms portDelta_mul_of_coprime
#print axioms isPPN_mul_squarefree_coprime_iff_portDelta_eq_one

end D5.S3.PrimeForms.PrimaryPseudoperfectPortComposition
