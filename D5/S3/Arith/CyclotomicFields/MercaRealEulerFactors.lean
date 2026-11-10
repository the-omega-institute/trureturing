/- GID: D5/S3/Arith/CyclotomicFields/MercaRealEulerFactors
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFields/MercaRealEulerFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual maximal-real Euler factors and the square of the normalized quartic character. -/

import D5.S3.Arith.CyclotomicFields.MercaQuadraticSubfield
import D5.S3.Arith.QuadraticFields.QuadraticPrimeSplitting
import D5.S3.Analytic.Zeta.PrimeQuadraticLValues

/-!
The half-integral maximal-order generator and quadratic reciprocity identify the
Euler factors of the actual maximal real subfield. Classical quadratic splitting
and the historical Ma--Zhang field identification are the sources; no class-number
identity is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped NumberField BigOperators

namespace D5.S3.Arith.CyclotomicFields.MercaRealEulerFactors

open NumberField Polynomial UniqueFactorizationMonoid
open MercaQuadraticSubfield MercaQuarticField
open D5.S3.ArithUnits.MercaQuarticCharacter
open D5.S3.Analytic.Zeta.PrimeQuadraticLValues
open D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal

attribute [local instance] Int.ideal_span_isMaximal_of_prime

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

/-- Squaring the normalized quartic character gives the genuine Legendre character. -/
theorem character_sq : character r hr ^ 2 = primeCharacter r := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod r)ˣ)
  have hfour : character r hr ^ 4 = 1 := (kernel_structure r hr).1 ▸ pow_orderOf_eq_one _
  have hs : (character r hr (g : ZMod r) ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, ← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
  have hχ : character r hr (g : ZMod r) ^ 2 = -1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · have he : character r hr ^ 2 = 1 := (MulChar.eq_iff hg _ _).mpr (by
        simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h)
      have hd := orderOf_dvd_of_pow_eq_one he
      rw [(kernel_structure r hr).1] at hd
      norm_num at hd
    · exact h
  have hψ : primeCharacter r (g : ZMod r) = -1 := by
    have hs := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (g : ZMod r))
      (primeCharacter_quadratic r).sq_eq_one
    simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hs
    rcases sq_eq_one_iff.mp hs with h | h
    · exact (primeCharacter_nontrivial r (by omega)
        ((MulChar.eq_iff hg _ _).mpr (by simpa only [MulChar.one_apply_coe] using h))).elim
    · exact h
  apply (MulChar.eq_iff hg _ _).mpr
  simpa only [MulChar.pow_apply_coe, hχ, hψ]

private abbrev RealField := maximalRealSubfield (MercaQuarticField.Field r hr)
private def a : ℤ := ((r - 1) / 4 : ℕ)
private def orderEquiv : QuadraticAlgebra ℤ (a r) 1 ≃ₐ[ℤ] 𝓞 (RealField r hr) :=
  (realMaximalOrderEquiv r hr).trans
    (((realEquiv r hr).restrictScalars ℤ).mapIntegralClosure)

private def generator : 𝓞 (RealField r hr) := orderEquiv r hr QuadraticAlgebra.omega

private lemma generator_exponent : RingOfIntegers.exponent (generator r hr) = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  have h := AlgHom.map_adjoin_singleton (orderEquiv r hr).toAlgHom
    (QuadraticAlgebra.omega : QuadraticAlgebra ℤ (a r) 1)
  rw [QuadraticAlgebra.adjoin_omega_eq_top, Algebra.map_top] at h
  exact h.symm.trans ((AlgHom.range_eq_top (orderEquiv r hr).toAlgHom).mpr
    (orderEquiv r hr).surjective)

private lemma generator_minpoly :
    minpoly ℤ (generator r hr) = X ^ 2 - X - C (a r) := by
  rw [generator, minpoly.algEquiv_eq, orderGenerator_minpoly, orderPolynomial]
  simp

private lemma generator_euler_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) p,
      (1 - z ^ f.natDegree)) =
    (1 - z) * (1 - primeCharacter r (p : ZMod r) * z) := by
  classical
  have hmap : (minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 - X - C (a r : ZMod p) := by rw [generator_minpoly]; simp
  change (∏ f ∈ (normalizedFactors
    ((minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod p)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap, quadratic_euler_polynomial ((ZMod.ringChar_zmod_n p).substr hp)]
  have hD : (1 : ZMod p) + 4 * (a r : ZMod p) = (r : ZMod p) := by
    have h : 1 + 4 * a r = (r : ℤ) := by dsimp [a]; omega
    simpa using congrArg (Int.castRingHom (ZMod p)) h
  rw [hD]
  have hχ : quadraticChar (ZMod p) (r : ZMod p) = quadraticChar (ZMod r) (p : ZMod r) := by
    simpa only [legendreSym, Int.cast_natCast] using
      (legendreSym.quadratic_reciprocity_one_mod_four (p := r) (q := p) (by omega) hp)
  rw [hχ]
  rfl

private lemma generator_euler_two (z : ℂ) :
    (∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) 2,
      (1 - z ^ f.natDegree)) =
    (1 - z) * (1 - primeCharacter r (2 : ZMod r) * z) := by
  classical
  have ha : a r % 2 = 1 := by dsimp [a]; omega
  have haz : (a r : ZMod 2) = 1 := by
    rw [← ZMod.intCast_mod (a r) 2]
    norm_num only [Nat.cast_ofNat]
    rw [ha]
    norm_num
  have hmap : (minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod 2)) =
      X ^ 2 - X - C (1 : ZMod 2) := by
    rw [generator_minpoly]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    change X ^ 2 - X - C (a r : ZMod 2) = _
    rw [haz]
  have hχ : primeCharacter r (2 : ZMod r) = -1 := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (2 : ZMod r)) (character_sq r hr)
    rw [MulChar.pow_apply' _ (by decide : 2 ≠ 0), (kernel_structure r hr).2.1,
      Complex.I_sq] at h
    exact h.symm
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
  change (∏ f ∈ (normalizedFactors
    ((minpoly ℤ (generator r hr)).map (Int.castRingHom (ZMod 2)))).toFinset,
      (1 - z ^ f.natDegree)) = _
  rw [hmap, normalizedFactors_irreducible hirr, hmonic.normalize_eq_self]
  simp only [Multiset.toFinset_singleton, Finset.prod_singleton, hdeg, hχ]
  ring

/-- The actual maximal-real field Euler polynomial at every rational prime. -/
theorem euler_polynomial (p : ℕ) [Fact p.Prime] (z : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (RealField r hr)),
      (1 - z ^ P.val.inertiaDeg ℤ)) =
    (1 - z) * (1 - (character r hr (p : ZMod r)) ^ 2 * z) := by
  classical
  have hexp : ¬p ∣ RingOfIntegers.exponent (generator r hr) := by
    rw [generator_exponent]; exact (Fact.out : p.Prime).not_dvd_one
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp
  have he : (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (RealField r hr)),
      (1 - z ^ P.val.inertiaDeg ℤ)) =
    ∏ f ∈ RingOfIntegers.monicFactorsMod (generator r hr) p, (1 - z ^ f.natDegree) := by
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
  rw [he, ← MulChar.pow_apply' _ (by decide : 2 ≠ 0), character_sq]
  by_cases hp : p = 2
  · subst p; exact generator_euler_two r hr z
  · exact generator_euler_odd r hr p hp z

end D5.S3.Arith.CyclotomicFields.MercaRealEulerFactors
