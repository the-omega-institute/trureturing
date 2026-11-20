/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every earlier block prime splits in the actual later native residue algebra. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclicOrder
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic

set_option autoImplicit false
open Polynomial D5.S1.Scale NumberField
open D5.S3.Factorization.QuadraticIdeals
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open scoped NumberField BigOperators

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting

/-- A native block divisible by a modulus forces the next Lucas
coordinate, and every later coordinate, to vanish at that modulus. -/
theorem later_lucas_vanishes {R : Type*} [CommRing R] (i j : ℕ)
    (hi : 1 ≤ i) (hij : i < j)
    (hB : ((goldenLucas (3 ^ i) : R) ^ 2 + 3) = 0) :
    (goldenLucas (3 ^ j) : R) = 0 := by
  have next (n : ℕ) (hn : 1 ≤ n) :
      (goldenLucas (3 ^ (n + 1)) : R) =
        (goldenLucas (3 ^ n) : R) * ((goldenLucas (3 ^ n) : R) ^ 2 + 3) := by
    have hc := congrArg (Int.castRingHom R) (golden_cubic_lucas_block n hn).2.2.2.2.2
    simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hc
  obtain ⟨a, ha⟩ : ∃ a : ℕ, j = i + 1 + a := ⟨j - (i + 1), by omega⟩
  subst j
  induction a with
  | zero => simp [next i hi, hB]
  | succ a ih =>
    change (goldenLucas (3 ^ ((i + 1 + a) + 1)) : R) = 0
    rw [next _ (by omega), ih (by omega), zero_mul]

/-- Later blocks have a uniform, explicit factorization of their cubic
reduction. The roots are simple when the modulus is a prime larger than 3. -/
theorem later_cubic_map_eq {p i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hB : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 3) :
    (cubic (goldenLucas (3 ^ j))).toPoly.map (Int.castRingHom (ZMod p)) =
      X * (X - C 3) * (X + C 3) := by
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hB
  have hb' : ((goldenLucas (3 ^ i) : ZMod p) ^ 2 + 3) = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hb
  have hl := later_lucas_vanishes i j hi hij hb'
  have hL : (goldenLucas (3 ^ j) : (ZMod p)[X]) = 0 := by
    simpa only [map_intCast, map_zero] using congrArg (C : ZMod p →+* (ZMod p)[X]) hl
  simp [cubic, Cubic.toPoly, hL, Polynomial.C_ofNat]
  ring

/-- The three displayed roots cannot collide at a prime larger than three. -/
theorem later_cubic_roots_distinct {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    (0 : ZMod p) ≠ 3 ∧ (0 : ZMod p) ≠ -3 ∧ (3 : ZMod p) ≠ -3 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    have h : ¬p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by decide) hp
    exact fun he => h ((ZMod.natCast_eq_zero_iff _ p).mp he)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    exact fun he => h ((ZMod.natCast_eq_zero_iff _ p).mp he)
  refine ⟨Ne.symm h3, Ne.symm (neg_ne_zero.mpr h3), ?_⟩
  intro hh
  apply mul_ne_zero h2 h3
  linear_combination hh

theorem exponent_prime_of_clear {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) {p : ℕ} [Fact p.Prime] {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d)
    (hclear : ∀ z : K, IsIntegral ℤ z →
      d • z ∈ Algebra.adjoin ℤ ({(α : K)} : Set K)) :
    ¬ p ∣ RingOfIntegers.exponent α := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  let A := Ideal.comap (algebraMap ℤ (𝓞 K)) (conductor ℤ α)
  have hda : d ∈ A := by
    change algebraMap ℤ (𝓞 K) d ∈ conductor ℤ α
    rw [mem_conductor_iff]
    intro z
    let f : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
    have hzr : d • (z : K) ∈ (Algebra.adjoin ℤ ({α} : Set (𝓞 K))).map f := by
      rw [AlgHom.map_adjoin_singleton]
      exact hclear _ z.isIntegral_coe
    obtain ⟨s, hs, he⟩ := hzr
    have hsz : s = algebraMap ℤ (𝓞 K) d * z := by
      apply RingOfIntegers.coe_injective
      change f s = f (algebraMap ℤ (𝓞 K) d * z)
      change f s = d • (z : K) at he
      rw [he, map_mul, AlgHom.commutes, Algebra.smul_def]
      rfl
    rwa [hsz] at hs
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hc : IsCoprime d (p : ℤ) := (hp.coprime_iff_not_dvd.mpr hd).symm
  obtain ⟨u, v, huv⟩ := hc
  apply codisjoint_iff.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  have h1 : u * d ∈ A ⊔ Ideal.span ({(p : ℤ)} : Set ℤ) := Ideal.mem_sup_left (A.mul_mem_left u hda)
  have h2 : v * (p : ℤ) ∈ A ⊔ Ideal.span ({(p : ℤ)} : Set ℤ) := Ideal.mem_sup_right ((Ideal.span ({(p : ℤ)} : Set ℤ)).mul_mem_left v (Ideal.subset_span rfl))
  rw [← huv]
  exact (A ⊔ Ideal.span ({(p : ℤ)} : Set ℤ)).add_mem h1 h2


noncomputable def distinct_linear_quotient {F I : Type*} [Field F] [Fintype I]
    (r : I → F) (hr : Function.Injective r) :
    (F[X] ⧸ Ideal.span ({∏ i, (X - C (r i))} : Set F[X])) ≃+* (I → F) := by
  classical
  let J (i : I) : Ideal F[X] := Ideal.span {X - C (r i)}
  have hJ : Pairwise (Function.onFun IsCoprime J) := by
    intro i j hij
    have h := isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr (hr.ne hij)).isUnit
    rw [Function.onFun, show J i = Ideal.span {X - C (r i)} by rfl,
      show J j = Ideal.span {X - C (r j)} by rfl]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr h
  have hs : Ideal.span ({∏ i, (X - C (r i))} : Set F[X]) = ⨅ i, J i := by
    calc
      _ = ∏ i, J i := by
        have hf (u : Finset I) :
            Ideal.span ({∏ i ∈ u, (X - C (r i))} : Set F[X]) = ∏ i ∈ u, J i := by
          induction u using Finset.induction with
          | empty => simp [Ideal.span_singleton_one]
          | insert a s hs ih =>
            rw [Finset.prod_insert hs, Finset.prod_insert hs, ← ih]
            exact (Ideal.span_singleton_mul_span_singleton _ _).symm
        exact hf Finset.univ
      _ = _ := by
        simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
          (s := Finset.univ) (J := J) (hJ.set_pairwise _)
  exact (Ideal.quotEquivOfEq hs).trans ((Ideal.quotientInfRingEquivPiQuotient J hJ).trans
    (RingEquiv.piCongrRight fun i => (Polynomial.quotientSpanXSubCAlgEquiv (r i)).toRingEquiv))

private theorem integer_cubic_aeval {F : Type*} [Field F] (l : ℤ) (x : F) :
    aeval x (cubic l).toPoly = equation (l : F) x := by
  have hc : eval₂ (Int.castRingHom F) x (l : ℤ[X]) = (l : F) := map_intCast (eval₂RingHom (Int.castRingHom F) x) l
  have hcp : eval₂ (Int.castRingHom F) x ((l : ℤ[X]) ^ 2) = (l : F) ^ 2 := by
    rw [eval₂_pow, hc]
  simp [cubic, Cubic.toPoly, equation, Polynomial.aeval_def, hcp, hc]
  ring

theorem native_conductor_witness (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3 ^ j)
    let f := (cubic (l : ℚ)).toPoly
    let K := f.SplittingField
    ∃ α : 𝓞 K,
      minpoly ℤ α = (cubic l).toPoly ∧
      ∀ p : ℕ, 3 < p → (p.Prime) →
        ((l : ZMod p) ^ 2 + 3) ≠ 0 →
        ¬ p ∣ RingOfIntegers.exponent α := by
  classical
  let l := goldenLucas (3 ^ j)
  let f := (cubic (l : ℚ)).toPoly
  let K := f.SplittingField
  let _ : NumberField K := ⟨⟩
  obtain ⟨x, S, b, hx, hSint, hspan, hb0, hb1, hb2, hdiscr⟩ := GoldenCubicNativeCyclicOrder.actual_order_discriminant j hj
  have hint (i : Fin 3) : IsIntegral ℤ (b i) := by
    apply hSint
    change b i ∈ S.toSubmodule
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hαint : IsIntegral ℤ x := by simpa only [hb1] using hint 1
  let α : 𝓞 K := ⟨x, hαint⟩
  have hmon : (cubic l).toPoly.Monic := Cubic.monic_of_a_eq_one rfl
  have hmap : (cubic l).toPoly.map (Int.castRingHom ℚ) = f := by
    simp [f, cubic, Cubic.toPoly, Polynomial.C_ofNat]
  have hirr : Irreducible (cubic l).toPoly := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mpr
      (hmap ▸ rational_irreducible l (native_lucas_mod j hj).1)
  have hroot : Polynomial.aeval x (cubic l).toPoly = 0 := by
    exact (integer_cubic_aeval (F := K) l x).trans hx
  have hmin : (cubic l).toPoly = minpoly ℤ x := by
    obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hαint hroot
    refine Polynomial.eq_of_monic_of_associated hmon (minpoly.monic hαint) ?_
    exact mul_one (minpoly ℤ x) ▸ hg.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 ((hirr.isUnit_or_isUnit hg).resolve_left
        (minpoly.not_isUnit ℤ x)))
  refine ⟨α, (RingOfIntegers.minpoly_coe α).symm.trans hmin.symm, ?_⟩
  intro p hp hpp hB
  let _ : Fact p.Prime := ⟨hpp⟩
  let B := l ^ 2 + 3
  let D : ℤ := 81 * B ^ 2
  have hd : Algebra.discr ℚ b = (D : ℚ) := by
    simpa only [D, B, l, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hdiscr
  have hdvd : ¬ (p : ℤ) ∣ (2 * D) := by
    intro h
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * D) p).mpr h
    have h2 : (2 : ZMod p) ≠ 0 := fun he =>
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2<p))
        ((ZMod.natCast_eq_zero_iff 2 p).mp he)
    have h3 : (3 : ZMod p) ≠ 0 := fun he =>
      (Nat.not_dvd_of_pos_of_lt (by decide) hp)
        ((ZMod.natCast_eq_zero_iff 3 p).mp he)
    have h81 : (81 : ZMod p) ≠ 0 := by
      rw [show (81 : ZMod p) = 3 ^ 4 by norm_num]
      exact pow_ne_zero _ h3
    have hcast : ((2 * D : ℤ) : ZMod p) =
        2 * 81 * ((l : ZMod p) ^ 2 + 3) ^ 2 := by simp [D, B]; ring
    rw [hcast] at hc
    exact mul_ne_zero (mul_ne_zero h2 h81) (pow_ne_zero _ hB) hc
  apply exponent_prime_of_clear α hdvd
  intro z hz
  have hm := CubicIntegralLattice.discr_smul_mem_integral_span b hint hz
  rw [hd, Int.cast_smul_eq_zsmul] at hm
  have hstep : ∀ y ∈ Submodule.span ℤ (Set.range b),
      (2 : ℤ) • y ∈ Algebra.adjoin ℤ ({x}:Set K) := by
    intro y hy
    let W := Algebra.adjoin ℤ ({x}:Set K)
    have hxW : x ∈ W := Algebra.subset_adjoin rfl
    refine Submodule.span_induction (p := fun y _ => (2 : ℤ) • y ∈ W) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · change (2 : ℤ) • b 0 ∈ W
        rw [hb0, zsmul_one]
        exact W.intCast_mem 2
      · change (2 : ℤ) • b 1 ∈ W
        rw [hb1]
        exact W.toSubmodule.smul_mem 2 hxW
      · change (2 : ℤ) • b 2 ∈ W
        have hw : (2 : ℤ) • b 2 = x ^ 2 - x := by
          rw [hb2]
          simp [Algebra.smul_def]
          ring
        rw [hw]
        exact W.sub_mem (W.pow_mem hxW 2) hxW
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact W.add_mem ha hb
    · intro a w _ hw
      rw [smul_comm]
      exact W.toSubmodule.smul_mem a hw
  rw [mul_smul]
  exact hstep _ hm
/-- A prime greater than three that divides an earlier Lucas block has
completely split residue algebra in every later native cyclic field. -/
theorem earlier_prime_residue_product {p i j : ℕ}
    (hpp : p.Prime) (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 3) :
    let f := (cubic (goldenLucas (3 ^ j) : ℚ)).toPoly
    let K := f.SplittingField
    Nonempty ((𝓞 K ⧸ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) ≃+* (Fin 3 → ZMod p)) := by
  let l := goldenLucas (3 ^ j)
  let f := (cubic (l : ℚ)).toPoly
  let K := f.SplittingField
  let _ : NumberField K := ⟨⟩
  let _ : Fact p.Prime := ⟨hpp⟩
  change Nonempty ((𝓞 K ⧸ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) ≃+* (Fin 3 → ZMod p))
  obtain ⟨α, hmin, hgood⟩ := native_conductor_witness j (by omega)
  have hb : ((goldenLucas (3 ^ i) : ZMod p) ^ 2 + 3) = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hB
  have hl : (l : ZMod p) = 0 := later_lucas_vanishes i j hi hij hb
  have h3 : (3 : ZMod p) ≠ 0 := fun he =>
    (Nat.not_dvd_of_pos_of_lt (by decide) hp) ((ZMod.natCast_eq_zero_iff 3 p).mp he)
  have hx : ¬ p ∣ RingOfIntegers.exponent α := hgood p hp hpp (show (l : ZMod p) ^ 2 + 3 ≠ 0 by rw [hl]; simpa using h3)
  let r : Fin 3 → ZMod p := ![0, 3, -3]
  obtain ⟨h03, h0n, h3n⟩ := later_cubic_roots_distinct hp
  have hr : Function.Injective r := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [r, ne_comm, Fin.isValue]
  have hpoly : (minpoly ℤ α).map (Int.castRingHom (ZMod p)) =
      ∏ a, (X - C (r a)) := by
    rw [hmin, later_cubic_map_eq hi hij hB, Fin.prod_univ_three]
    simp [r, C_neg, sub_eq_add_neg]
  have hq := (RingOfIntegers.ZModXQuotSpanEquivQuotSpan hx).symm
  rw [hpoly] at hq
  exact ⟨hq.trans (distinct_linear_quotient r hr)⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting
