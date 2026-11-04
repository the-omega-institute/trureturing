/- GID: D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/QuadraticPrimeSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic reciprocity identifies roots of the actual maximal-order polynomial. -/

import D5.S3.Arith.QuadraticFields.QuadraticOrderGenerator
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal

open Polynomial UniqueFactorizationMonoid
open scoped NumberField

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-- Completing the square is a genuine bijection of root types in every odd field. -/
def quadraticRootEquivSqrts {F : Type*} [Field F] (hF : ringChar F ≠ 2) (a : F) :
    {x : F // x ^ 2 - x - a = 0} ≃ {y : F // y ^ 2 = 1 + 4 * a} where
  toFun x := ⟨2 * x.1 - 1, by
    calc
      (2 * x.1 - 1) ^ 2 = 4 * (x.1 ^ 2 - x.1 - a) + (1 + 4 * a) := by ring
      _ = 1 + 4 * a := by rw [x.2]; ring⟩
  invFun y := ⟨(y.1 + 1) / 2, by
    have h4 : (4 : F) ≠ 0 := by
      convert mul_ne_zero (Ring.two_ne_zero hF) (Ring.two_ne_zero hF) using 1 <;> norm_num
    calc
      ((y.1 + 1) / 2) ^ 2 - (y.1 + 1) / 2 - a =
          (y.1 ^ 2 - (1 + 4 * a)) / 4 := by
        field_simp [Ring.two_ne_zero hF, h4]
        ring
      _ = 0 := by rw [y.2, sub_self, zero_div]⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    field_simp [Ring.two_ne_zero hF]
    ring
  right_inv y := by
    apply Subtype.ext
    dsimp
    field_simp [Ring.two_ne_zero hF]
    ring

/-- Root count for the half-integral quadratic generator, including the ramified case. -/
theorem quadratic_root_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a : F) :
    (Fintype.card {x : F // x ^ 2 - x - a = 0} : ℤ) =
      quadraticChar F (1 + 4 * a) + 1 := by
  rw [Fintype.card_congr (quadraticRootEquivSqrts hF a)]
  simpa [Fintype.card_subtype] using quadraticChar_card_sqrts hF (1 + 4 * a)

private theorem generator_polynomial_factor {F : Type*} [Field F]
    (hF : ringChar F ≠ 2) (a s : F) (hs : s ^ 2 = 1 + 4 * a) :
    (X ^ 2 - X - C a : F[X]) =
      (X - C ((1 + s) / 2)) * (X - C ((1 - s) / 2)) := by
  have h4 : (4 : F) ≠ 0 := by
    convert mul_ne_zero (Ring.two_ne_zero hF) (Ring.two_ne_zero hF) using 1 <;> norm_num
  have hsum : (1 + s) / 2 + (1 - s) / 2 = 1 := by
    field_simp [Ring.two_ne_zero hF]
    ring
  have hprod : ((1 + s) / 2) * ((1 - s) / 2) = -a := by
    calc
      _ = (1 - s ^ 2) / 4 := by field_simp [Ring.two_ne_zero hF, h4]; ring
      _ = -a := by rw [hs]; field_simp [h4]; ring
  calc
    _ = X ^ 2 - C ((1 + s) / 2 + (1 - s) / 2) * X +
        C (((1 + s) / 2) * ((1 - s) / 2)) := by rw [hsum, hprod]; simp [sub_eq_add_neg]
    _ = _ := by simp only [map_add, map_mul]; ring

/-- The product over distinct irreducible factors is the local Euler polynomial.
Repeated factors contribute only once, so this also handles ramified primes. -/
theorem quadratic_euler_polynomial {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a : F) (z : ℂ) :
    (∏ f ∈ (UniqueFactorizationMonoid.normalizedFactors
      (X ^ 2 - X - C a : F[X])).toFinset, (1 - z ^ f.natDegree)) =
        (1 - z) * (1 - (quadraticChar F (1 + 4 * a) : ℂ) * z) := by
  classical
  have hnf (u : F) : normalizedFactors (X - C u : F[X]) = {X - C u} := by
    rw [normalizedFactors_irreducible (irreducible_X_sub_C u),
      (monic_X_sub_C u).normalize_eq_self]
  by_cases hD : 1 + 4 * a = 0
  · have hfac := generator_polynomial_factor hF a 0 (by simpa using hD.symm)
    simp only [add_zero, sub_zero] at hfac
    rw [hfac, normalizedFactors_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero]
    simp [hnf, hD]
  · rcases quadraticChar_dichotomy hD with hpos | hneg
    · have hsq := (quadraticChar_one_iff_isSquare hD).mp hpos
      obtain ⟨s, hs⟩ := hsq
      have hss : s ^ 2 = 1 + 4 * a := by simpa only [sq] using hs.symm
      have hs0 : s ≠ 0 := by
        intro h
        apply hD
        rw [← hss, h, zero_pow two_ne_zero]
      have huv : (1 + s) / 2 ≠ (1 - s) / 2 := by
        intro h
        have h' : 1 + s = 1 - s := (div_left_inj' (Ring.two_ne_zero hF)).mp h
        have hz : 2 * s = 0 := by linear_combination h'
        exact hs0 ((mul_eq_zero.mp hz).resolve_left (Ring.two_ne_zero hF))
      have hfg : (X - C ((1 + s) / 2) : F[X]) ≠ X - C ((1 - s) / 2) := by
        intro h
        have h' := congrArg (fun f : F[X] => f.coeff 0) h
        simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at h'
        exact huv (neg_injective h')
      rw [generator_polynomial_factor hF a s hss,
        normalizedFactors_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero]
      simp [hnf, hfg, hpos]
    · have hmonic : (X ^ 2 - X - C a : F[X]).Monic := by
        rw [show (X ^ 2 - X - C a : F[X]) = X ^ 2 - (X + C a) by ring]
        apply monic_X_pow_sub
        simpa using! (degree_linear_lt (a := (1 : F)) (b := a))
      have hdeg : (X ^ 2 - X - C a : F[X]).natDegree = 2 := by
        simpa only [C_1, C_neg, one_mul, neg_one_mul, sub_eq_add_neg] using
          (natDegree_quadratic (a := (1 : F)) (b := -1) (c := -a) one_ne_zero)
      have hirr : Irreducible (X ^ 2 - X - C a : F[X]) := by
        apply irreducible_of_degree_le_three_of_not_isRoot (by rw [Finset.mem_Icc, hdeg]; norm_num)
        intro x hx
        have hx' : x ^ 2 - x - a = 0 := by simpa [Polynomial.IsRoot] using hx
        let y := quadraticRootEquivSqrts hF a ⟨x, hx'⟩
        exact (quadraticChar_neg_one_iff_not_isSquare.mp hneg)
          ⟨y.1, by simpa only [sq] using y.2.symm⟩
      rw [normalizedFactors_irreducible hirr, hmonic.normalize_eq_self]
      simp [hdeg, hneg]
      ring

namespace PrimeImaginary

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The discriminant character is the conductor-p quadratic character, including at p.
The prime two is treated separately because the integral generator has denominator two. -/
theorem negative_prime_reciprocity (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    legendreSym ℓ (-(p : ℤ)) = legendreSym p (ℓ : ℤ) := by
  have hp4 : p % 4 = 3 := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hs : (-1 : ℤ) ^ (p / 2) = -1 :=
    ZMod.neg_one_pow_div_two_of_three_mod_four hp4
  have hℓodd : ℓ % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : ℓ.Prime).odd_of_ne_two hℓ)
  rw [legendreSym.at_neg hℓ, ZMod.χ₄_eq_neg_one_pow hℓodd,
    legendreSym.quadratic_reciprocity' hp2 hℓ, pow_mul, hs]
  have he : ((-1 : ℤ) ^ (ℓ / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (ℓ / 2) 2, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℤ) ^ (ℓ / 2)) ^ 2 * legendreSym p (ℓ : ℤ) := by ring
    _ = _ := by rw [he, one_mul]

/-- The roots of the actual integral generator polynomial at each odd rational prime.
This identifies its linear factors using the same character as the original double sum. -/
theorem integralGenerator_root_card (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    (Fintype.card {x : ZMod ℓ //
      ((minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod ℓ))).IsRoot x} : ℤ) =
        legendreSym p (ℓ : ℤ) + 1 := by
  have he : {x : ZMod ℓ //
      ((minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod ℓ))).IsRoot x} ≃
      {x : ZMod ℓ // x ^ 2 - x - (orderA p : ZMod ℓ) = 0} :=
    Equiv.subtypeEquivRight fun x => by
      simp [integralGenerator_minpoly, Polynomial.IsRoot]
  rw [Fintype.card_congr he,
    quadratic_root_card ((ZMod.ringChar_zmod_n ℓ).substr hℓ)]
  have hD : (1 : ZMod ℓ) + 4 * (orderA p : ZMod ℓ) = -(p : ZMod ℓ) := by
    have h := congrArg (Int.castRingHom (ZMod ℓ))
      (show 1 + 4 * orderA p = -(p : ℤ) by
        simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p)
    simpa using h
  rw [hD]
  simpa only [legendreSym, Int.cast_neg, Int.cast_natCast] using
    congrArg (fun v : ℤ => v + 1) (negative_prime_reciprocity p ℓ hℓ)

/-- The local factor supplied to Kummer-Dedekind is expressed by the original
conductor-p character, at every odd prime including the ramified prime p. -/
theorem integralGenerator_euler_polynomial (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (integralGenerator p) ℓ,
      (1 - z ^ f.natDegree)) =
        (1 - z) * (1 - (legendreSym p (ℓ : ℤ) : ℂ) * z) := by
  classical
  have hmap : (minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod ℓ)) =
      X ^ 2 - X - C (orderA p : ZMod ℓ) := by
    rw [integralGenerator_minpoly]
    simp
  change (∏ f ∈ (normalizedFactors
      ((minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod ℓ)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap, quadratic_euler_polynomial ((ZMod.ringChar_zmod_n ℓ).substr hℓ)]
  have hD : (1 : ZMod ℓ) + 4 * (orderA p : ZMod ℓ) = -(p : ZMod ℓ) := by
    have h := congrArg (Int.castRingHom (ZMod ℓ))
      (show 1 + 4 * orderA p = -(p : ℤ) by
        simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p)
    simpa using h
  rw [hD]
  have hχ : quadraticChar (ZMod ℓ) (-(p : ZMod ℓ)) = legendreSym p (ℓ : ℤ) := by
    simpa only [legendreSym, Int.cast_neg, Int.cast_natCast] using
      negative_prime_reciprocity p ℓ hℓ
  rw [hχ]

/-- At two the half-integral polynomial is irreducible for p congruent to three mod eight
and has two distinct linear factors for p congruent to seven mod eight. -/
theorem integralGenerator_euler_polynomial_two (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (integralGenerator p) 2,
      (1 - z ^ f.natDegree)) =
        (1 - z) * (1 - (legendreSym p 2 : ℂ) * z) := by
  classical
  have hp4 : p % 4 = 3 := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hA : 1 + 4 * orderA p = -(p : ℤ) := by
    simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p
  have hmap : (minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod 2)) =
      X ^ 2 - X - C (orderA p : ZMod 2) := by
    rw [integralGenerator_minpoly]
    simp
  have hnf (u : ZMod 2) : normalizedFactors (X - C u : (ZMod 2)[X]) = {X - C u} := by
    rw [normalizedFactors_irreducible (irreducible_X_sub_C u),
      (monic_X_sub_C u).normalize_eq_self]
  change (∏ f ∈ (normalizedFactors
      ((minpoly ℤ (integralGenerator p)).map (Int.castRingHom (ZMod 2)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap]
  have hp8 : p % 8 = 3 ∨ p % 8 = 7 := by omega
  rcases hp8 with hp8 | hp8
  · have hp8z : (p : ℤ) % 8 = 3 := by exact_mod_cast hp8
    have ha : orderA p % 2 = 1 := by omega
    have haz : (orderA p : ZMod 2) = 1 := by
      rw [← ZMod.intCast_mod (orderA p) 2]
      norm_num only [Nat.cast_ofNat]
      rw [ha]
      norm_num
    have hχ : legendreSym p 2 = -1 := by
      rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight p, hp8]
      rfl
    have hdeg : (X ^ 2 - X - C (1 : ZMod 2)).natDegree = 2 := by
      simpa only [C_1, C_neg, one_mul, neg_one_mul, sub_eq_add_neg] using
        (natDegree_quadratic (a := (1 : ZMod 2)) (b := -1) (c := -1) one_ne_zero)
    have hmonic : (X ^ 2 - X - C (1 : ZMod 2)).Monic := by
      rw [show (X ^ 2 - X - C (1 : ZMod 2)) = X ^ 2 - (X + C 1) by ring]
      apply monic_X_pow_sub
      simpa using! (degree_linear_lt (a := (1 : ZMod 2)) (b := 1))
    have hirr : Irreducible (X ^ 2 - X - C (1 : ZMod 2)) := by
      apply irreducible_of_degree_le_three_of_not_isRoot (by rw [Finset.mem_Icc, hdeg]; norm_num)
      intro x hx
      have hx' : x ^ 2 - x - (1 : ZMod 2) = 0 := by
        simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C] using hx
      have hsq : ∀ y : ZMod 2, y ^ 2 = y := by decide
      rw [hsq, sub_self, zero_sub, neg_eq_zero] at hx'
      exact one_ne_zero hx'
    rw [haz, normalizedFactors_irreducible hirr, hmonic.normalize_eq_self]
    simp only [Multiset.toFinset_singleton, Finset.prod_singleton, hdeg, hχ,
      Int.cast_neg, Int.cast_one]
    ring
  · have hp8z : (p : ℤ) % 8 = 7 := by exact_mod_cast hp8
    have ha : orderA p % 2 = 0 := by omega
    have haz : (orderA p : ZMod 2) = 0 := by
      rw [← ZMod.intCast_mod (orderA p) 2]
      norm_num only [Nat.cast_ofNat]
      rw [ha]
      norm_num
    have hχ : legendreSym p 2 = 1 := by
      rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight p, hp8]
      rfl
    have hfac : (X ^ 2 - X - C (0 : ZMod 2)) = (X - C 0) * (X - C 1) := by
      simp
      ring
    have hfg : (X - C (0 : ZMod 2)) ≠ X - C 1 := by
      intro h
      have := congrArg (fun f : (ZMod 2)[X] => f.coeff 0) h
      norm_num at this
    rw [haz, hfac, normalizedFactors_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero,
      hnf, hnf]
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union]
    rw [Finset.prod_insert (by simpa only [Finset.mem_singleton] using hfg),
      Finset.prod_singleton]
    simp only [natDegree_X_sub_C, pow_one, hχ, Int.cast_one, one_mul]

/-- Every rational prime, including two and the ramified prime p. -/
theorem integralGenerator_euler_polynomial_all (ℓ : ℕ) [Fact ℓ.Prime] (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (integralGenerator p) ℓ,
      (1 - z ^ f.natDegree)) =
        (1 - z) * (1 - (legendreSym p (ℓ : ℤ) : ℂ) * z) := by
  by_cases hℓ : ℓ = 2
  · subst ℓ
    exact integralGenerator_euler_polynomial_two p z
  · exact integralGenerator_euler_polynomial p ℓ hℓ z

/-- Actual prime ideals over every rational prime have the quadratic Euler factor.
The maximal-order generator theorem discharges the index condition at every prime. -/
theorem primeIdeal_euler_polynomial (ℓ : ℕ) [Fact ℓ.Prime] (z : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(ℓ : ℤ)}) (𝓞 (Field p)),
      (1 - z ^ Ideal.inertiaDeg (P : Ideal (𝓞 (Field p))) ℤ)) =
        (1 - z) * (1 - (legendreSym p (ℓ : ℤ) : ℂ) * z) := by
  classical
  have hexp : ¬ℓ ∣ RingOfIntegers.exponent (integralGenerator p) := by
    rw [integralGenerator_exponent]
    exact (Fact.out : ℓ.Prime).not_dvd_one
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp
  calc
    _ = ∏ f : RingOfIntegers.monicFactorsMod (integralGenerator p) ℓ,
        (1 - z ^ (f : (ZMod ℓ)[X]).natDegree) := by
      symm
      apply Fintype.prod_equiv e.symm
      intro f
      rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hexp f.property]
    _ = ∏ f ∈ RingOfIntegers.monicFactorsMod (integralGenerator p) ℓ,
        (1 - z ^ f.natDegree) := by
      simpa using (Finset.prod_coe_sort
        (RingOfIntegers.monicFactorsMod (integralGenerator p) ℓ)
        (fun f : (ZMod ℓ)[X] => 1 - z ^ f.natDegree))
    _ = _ := integralGenerator_euler_polynomial_all p ℓ z

end PrimeImaginary

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
