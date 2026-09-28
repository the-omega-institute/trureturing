/- GID: D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge
   generality: G
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Eisenstein quadratic algebra is the integral third cyclotomic ring. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open NumberField
open Polynomial

private noncomputable def eisensteinPowerBasis : PowerBasis ℤ EisensteinOrder where
  gen := QuadraticAlgebra.omega
  dim := 2
  basis := QuadraticAlgebra.basis (-1) (-1)
  basis_eq_pow := by
    intro i
    fin_cases i
    · apply (QuadraticAlgebra.basis (-1) (-1)).repr.injective
      ext j
      fin_cases j <;> simp [QuadraticAlgebra.basis_repr_apply,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · apply (QuadraticAlgebra.basis (-1) (-1)).repr.injective
      ext j
      fin_cases j <;> simp [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.omega]

/-- The Eisenstein quadratic order is the integral third cyclotomic algebra. -/
theorem eisenstein_cyclotomic_equiv_exists :
    Nonempty (EisensteinOrder ≃ₐ[ℤ] 𝓞 (CyclotomicField 3 ℚ)) := by
  refine ⟨?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hζ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)) (3 ^ 1) := by
    simpa only [pow_one] using
      (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))
  let pbE := eisensteinPowerBasis
  let pbO := hζ.integralPowerBasisOfPrimePow
  have hdimO : pbO.dim = 2 := by
    simpa only [pbO, pow_one, Nat.totient_prime Nat.prime_three, Nat.reduceSub] using
      hζ.integralPowerBasisOfPrimePow_dim
  have hrootE : aeval pbE.gen (cyclotomic 3 ℤ) = 0 := by
    rw [cyclotomic_three]
    simp only [map_add, map_pow, aeval_X, aeval_one]
    change (QuadraticAlgebra.omega : EisensteinOrder) ^ 2 +
      QuadraticAlgebra.omega + 1 = 0
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  have hrootO : aeval pbO.gen (cyclotomic 3 ℤ) = 0 := by
    rw [show pbO.gen = hζ.toInteger from hζ.integralPowerBasisOfPrimePow_gen]
    rw [← eval_map_algebraMap (cyclotomic 3 ℤ) hζ.toInteger, map_cyclotomic]
    exact hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic (by decide)
  have hmin (A : Type) [CommRing A] [Algebra ℤ A] (pb : PowerBasis ℤ A)
      (hdim : pb.dim = 2) (hroot : aeval pb.gen (cyclotomic 3 ℤ) = 0) :
      minpoly ℤ pb.gen = cyclotomic 3 ℤ := by
    have hdegree : (cyclotomic 3 ℤ).degree = (2 : WithBot ℕ) := by
      rw [degree_cyclotomic]
      norm_num [Nat.totient_prime Nat.prime_three]
    symm
    apply minpoly.unique' ℤ pb.gen (cyclotomic.monic 3 ℤ) hroot
    intro q hq
    by_cases hzero : q = 0
    · exact Or.inl hzero
    · right
      intro hqroot
      have hle := pb.dim_le_degree_of_root hzero hqroot
      rw [hdim] at hle
      rw [hdegree] at hq
      exact (not_le_of_gt hq) hle
  exact pbE.equivOfMinpoly pbO
    ((hmin EisensteinOrder pbE rfl hrootE).trans (hmin _ pbO hdimO hrootO).symm)

#print axioms eisenstein_cyclotomic_equiv_exists

end D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
