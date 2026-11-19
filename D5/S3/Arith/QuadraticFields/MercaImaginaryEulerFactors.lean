/- GID: D5/S3/Arith/QuadraticFields/MercaImaginaryEulerFactors
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/MercaImaginaryEulerFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual maximal-order Euler factors for the imaginary quadratic Merca field. -/

import D5.S3.Arith.QuadraticFields.MercaImaginaryQuadratic
import D5.S3.Arith.QuadraticFields.QuadraticPrimeSplitting
import D5.S3.Analytic.Zeta.MercaImaginaryCharacter

/-! Every rational prime is computed using the actual maximal integer ring. -/

set_option autoImplicit false
noncomputable section
open scoped NumberField BigOperators

namespace D5.S3.Arith.QuadraticFields.MercaImaginaryEulerFactors
open NumberField Polynomial UniqueFactorizationMonoid
open MercaImaginaryQuadratic QuadraticOrderMaximal
open D5.S3.Analytic.Zeta.MercaImaginaryCharacter
attribute [local instance] Int.ideal_span_isMaximal_of_prime

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

private def generator : 𝓞 (Field r) :=
  maximalOrderEquiv r hr QuadraticAlgebra.omega

private lemma generator_exponent : RingOfIntegers.exponent (generator r hr) = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  have h := AlgHom.map_adjoin_singleton (maximalOrderEquiv r hr).toAlgHom
    (QuadraticAlgebra.omega : QuadraticAlgebra ℤ (-(r : ℤ)) 0)
  rw [QuadraticAlgebra.adjoin_omega_eq_top, Algebra.map_top] at h
  exact h.symm.trans ((AlgHom.range_eq_top (maximalOrderEquiv r hr).toAlgHom).mpr
    (maximalOrderEquiv r hr).surjective)

private lemma generator_minpoly :
    minpoly ℤ (generator r hr) = X ^ 2 + C (r : ℤ) := by
  rw [generator, minpoly.algEquiv_eq, orderGenerator_minpoly, orderPolynomial]
  simp

private lemma generator_euler_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) p,
      (1 - z ^ f.natDegree)) =
      (1 - z) * (1 - character r (p : ZMod (4 * r)) * z) := by
  classical
  have hmap : (minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 - C (0 : ZMod p) * X - C (-(r : ZMod p)) := by
    rw [generator_minpoly]
    simp
  change (∏ f ∈ (normalizedFactors
    ((minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod p)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap, quadratic_euler_polynomial_general ((ZMod.ringChar_zmod_n p).substr hp)]
  have hχ : (quadraticChar (ZMod p) (-(r : ZMod p)) : ℂ) =
      character r (p : ZMod (4 * r)) := by
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four
      (p := r) (q := p) (by omega) hp
    have hn := legendreSym.at_neg hp (r : ℤ)
    have h : legendreSym p (-(r : ℤ)) = ZMod.χ₄ (p : ZMod 4) * legendreSym r (p : ℤ) := by
      rw [hn, hrec]
    rw [show (p : ZMod (4 * r)) = ((p : ℤ) : ZMod (4 * r)) by norm_cast,
      character_int]
    exact_mod_cast h
  simp only [zero_pow two_ne_zero, zero_add]
  have hfour : quadraticChar (ZMod p) (4 : ZMod p) = 1 := by
    apply (quadraticChar_one_iff_isSquare (by
      have ht := Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
      convert pow_ne_zero 2 ht using 1 <;> ring)).mpr
    exact ⟨2, by ring⟩
  rw [map_mul, hfour, one_mul, hχ]

private lemma generator_euler_two (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) 2,
      (1 - z ^ f.natDegree)) =
      (1 - z) * (1 - character r (2 : ZMod (4 * r)) * z) := by
  classical
  have hr2 : (r : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod r 2, show r % 2 = 1 by omega]
    rfl
  have hmap : (minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod 2)) =
      (X - C (1 : ZMod 2)) * (X - C 1) := by
    rw [generator_minpoly]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
    have hC : Polynomial.map (Int.castRingHom (ZMod 2)) (C (r : ℤ)) =
        C (r : ZMod 2) := Polynomial.map_C _
    rw [hC]
    rw [hr2, C_1]
    have hc : (2 : ZMod 2) = 0 := by decide
    have htwo : (2 : (ZMod 2)[X]) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (Polynomial.C (R := ZMod 2)) hc
    linear_combination htwo * X
  have hχ : character r (2 : ZMod (4 * r)) = 0 := by
    rw [show (2 : ZMod (4 * r)) = ((2 : ℤ) : ZMod (4 * r)) by norm_num,
      character_int]
    norm_num [ZMod.χ₄]
  change (∏ f ∈ (normalizedFactors
    ((minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod 2)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap, normalizedFactors_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero,
    normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self]
  simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.union_self,
    Finset.prod_singleton, natDegree_X_sub_C, pow_one, hχ, zero_mul, sub_zero, mul_one]

include hr in
/-- Actual maximal-order Euler polynomials, at all rational primes including two and r. -/
theorem euler_polynomial (p : ℕ) [Fact p.Prime] (z : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r)),
      (1 - z ^ P.val.inertiaDeg ℤ)) =
      (1 - z) * (1 - character r (p : ZMod (4 * r)) * z) := by
  classical
  have hexp : ¬p ∣ RingOfIntegers.exponent (generator r hr) := by
    rw [generator_exponent]
    exact (Fact.out : p.Prime).not_dvd_one
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp
  have he : (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r)),
      (1 - z ^ P.val.inertiaDeg ℤ)) =
      ∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) p,
        (1 - z ^ f.natDegree) := by
    calc
      _ = ∏ f : RingOfIntegers.monicFactorsMod (generator r hr) p,
          (1 - z ^ (f : (ZMod p)[X]).natDegree) := by
        symm
        apply Fintype.prod_equiv e.symm
        intro f
        rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
          hexp f.property]
      _ = _ := by
        simpa using (Finset.prod_coe_sort
          (RingOfIntegers.monicFactorsMod (generator r hr) p)
          (fun f : (ZMod p)[X] => 1 - z ^ f.natDegree))
  rw [he]
  by_cases hp : p = 2
  · subst p; exact generator_euler_two r hr z
  · exact generator_euler_odd r hr p hp z

end D5.S3.Arith.QuadraticFields.MercaImaginaryEulerFactors
