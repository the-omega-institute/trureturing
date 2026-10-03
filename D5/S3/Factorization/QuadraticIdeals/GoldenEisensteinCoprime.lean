/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenEisensteinCoprime
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenEisensteinCoprime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conjugate Eisenstein ideals of a cubic golden block are coprime. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime

open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

/-- The oriented Eisenstein factor of a cubic Lucas block and its conjugate
generate the unit ideal. -/
theorem golden_eisenstein_conjugate_coprime (j : ℕ) (hj : 1 ≤ j) :
    let eta : EisensteinOrder := ⟨-2, goldenLucas (3 ^ j) - 1⟩
    IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) := by
  let x : ℤ := goldenLucas (3 ^ j)
  let eta : EisensteinOrder := ⟨-2, x - 1⟩
  change IsCoprime (Ideal.span {eta}) (Ideal.span {star eta})
  have hx72 : (x : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
  have hdiv : (72 : ℤ) ∣ x - 4 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 4 x 72).mp (by simpa using hx72.symm)
  obtain ⟨k, hk⟩ := hdiv
  have hx : x = 4 + 72 * k := by omega
  have hbez : IsCoprime (x ^ 2 + 3) (x + 3) := by
    refine ⟨-(4 + 42 * k), 7 + (4 + 42 * k) * (x - 3), ?_⟩
    rw [hx]
    ring
  have hnorm : ((x ^ 2 + 3 : ℤ) : EisensteinOrder) = eta * star eta := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    change (QuadraticAlgebra.C (x ^ 2 + 3) : EisensteinOrder) =
      QuadraticAlgebra.C (QuadraticAlgebra.norm eta)
    congr 1
    simp only [QuadraticAlgebra.norm_def, eta]
    ring
  have hsum : ((x + 3 : ℤ) : EisensteinOrder) = -(eta + star eta) := by
    apply QuadraticAlgebra.ext
    · simp [eta, QuadraticAlgebra.re_ofNat, add_comm]
      ring
    · simp [eta, QuadraticAlgebra.im_ofNat]
  have hbezE := hbez.intCast (R := EisensteinOrder)
  rw [hnorm, hsum] at hbezE
  obtain ⟨u, v, huv⟩ := hbezE
  apply (Ideal.isCoprime_span_singleton_iff eta (star eta)).2
  refine ⟨u * star eta - v, -v, ?_⟩
  linear_combination huv

#print axioms golden_eisenstein_conjugate_coprime

end D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
