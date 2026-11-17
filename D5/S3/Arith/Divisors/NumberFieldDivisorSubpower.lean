/- GID: D5/S3/Arith/Divisors/NumberFieldDivisorSubpower
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/NumberFieldDivisorSubpower
   mirror-E: none(waiver:uniform-number-field-estimate)
   anchors: []
   utility: none
   digest: Uniform subpower bounds for bounded conjugate divisors in cubic number fields. -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The constants in this file are chosen before the number field. Small ideal norms
are controlled by the single finite quotient modulo a fixed factorial. For the
archimedean part, equal principal ideals and equal logarithmic boxes give a unit
whose conjugates belong to one fixed bounded set of algebraic integers in `ℂ`.
Neither a discriminant bound nor a regulator bound occurs.
-/

open scoped NumberField
open Finset NumberField

universe u

namespace D5.S3.Arith.Divisors.NumberFieldDivisorSubpower

private theorem ideal_factorization_prod {K : Type u} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (factorization I).prod (fun P a => P ^ a) = I := by
  rw [← Finsupp.prod_toMultiset, factorization,
    Multiset.toFinsupp_toMultiset]
  exact Ideal.prod_normalizedFactors_eq_self hI

private theorem ideal_factorization_le {K : Type u} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (h : I ∣ J) :
    factorization I ≤
      factorization J := by
  intro P
  exact Ideal.count_le_of_ideal_ge (Ideal.dvd_iff_le.mp h) hJ P

/-- A uniform, deliberately coarse bound for the number of ideals of small norm.
Every such ideal contains `T!`, and is therefore determined by a subset of the
finite quotient modulo `T!`. -/
private theorem small_norm_ideal_card {K : Type u} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (T : ℕ) (s : Finset (Ideal (𝓞 K)))
    (hs : ∀ I ∈ s, I ≠ ⊥ ∧ I.absNorm ≤ T) :
    s.card ≤ 2 ^ (T.factorial ^ 3) := by
  classical
  let A : Ideal (𝓞 K) := Ideal.span {(T.factorial : 𝓞 K)}
  have hA : A ≠ ⊥ := by
    change Ideal.span ({(T.factorial : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.factorial_ne_zero T)
  letI : Finite ((𝓞 K) ⧸ A) :=
    (Ideal.absNorm_ne_zero_iff A).mp (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  letI : Fintype ((𝓞 K) ⧸ A) := Fintype.ofFinite _
  have hnorm : Fintype.card ((𝓞 K) ⧸ A) = T.factorial ^ Module.finrank ℚ K := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    change (Ideal.span {(T.factorial : 𝓞 K)}).absNorm = _
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hcontains : ∀ I ∈ s, A ≤ I := by
    intro I hIs
    obtain ⟨hI, hIT⟩ := hs I hIs
    have hpos : 0 < I.absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    obtain ⟨a, ha⟩ := Nat.dvd_factorial hpos hIT
    apply (Ideal.span_singleton_le_iff_mem I).mpr
    rw [ha, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ I.absNorm_mem
  let f : Ideal (𝓞 K) → Set ((𝓞 K) ⧸ A) :=
    fun I => (I.map (Ideal.Quotient.mk A) : Set ((𝓞 K) ⧸ A))
  have hinj : Set.InjOn f (s : Set (Ideal (𝓞 K))) := by
    intro I hI J hJ hij
    have hmap : I.map (Ideal.Quotient.mk A) = J.map (Ideal.Quotient.mk A) :=
      SetLike.coe_injective hij
    have := congrArg (Ideal.comap (Ideal.Quotient.mk A)) hmap
    simpa only [Ideal.comap_map_mk (hcontains I hI),
      Ideal.comap_map_mk (hcontains J hJ)] using this
  calc
    s.card ≤ (Finset.univ : Finset (Set ((𝓞 K) ⧸ A))).card :=
      Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ (T.factorial ^ Module.finrank ℚ K) := by
      simp only [Finset.card_univ, Fintype.card_set, hnorm]
    _ ≤ 2 ^ (T.factorial ^ 3) := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      exact Nat.pow_le_pow_right (Nat.factorial_pos T) hd

/-- Ideal divisor subpower bounds, uniform in all number fields of degree at most
three. The factorial quotient bound avoids any field-dependent small-prime
constant. -/
theorem ideal_divisors_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ∀ s : Finset (Ideal (𝓞 K)), (∀ J ∈ s, J ∣ I) →
      (s.card : ℝ) ≤ C * (I.absNorm : ℝ) ^ δ := by
  classical
  let r : ℝ := (2 : ℝ) ^ δ
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  obtain ⟨T, hT⟩ := exists_nat_gt ((2 : ℝ) ^ δ⁻¹)
  let B : ℕ := 2 ^ (T.factorial ^ 3)
  refine ⟨c ^ B, pow_pos (zero_lt_one.trans_le hc) _, ?_⟩
  intro K _ _ hd I hI s hs
  let a := factorization I
  have haP : ∀ P ∈ a.support, P ≠ ⊥ ∧ 2 ≤ P.absNorm := by
    intro P hP
    have hirr : Irreducible P :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor P
        (by simpa only [a, support_factorization,
          Multiset.mem_toFinset] using hP)
    have hn : P.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hirr.ne_zero
    have hnone : P.absNorm ≠ 1 := by
      intro h
      exact hirr.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
    exact ⟨hirr.ne_zero, by omega⟩
  have hcard : s.card ≤ (Finset.Iic a).card := by
    apply Finset.card_le_card_of_injOn
      (fun J => factorization J)
    · intro J hJ
      exact Finset.mem_Iic.mpr (ideal_factorization_le hI (hs J hJ))
    · intro J hJ L hL heq
      apply associated_iff_eq.mp
      exact associated_of_factorization_eq J L
        (ne_zero_of_dvd_ne_zero hI (hs J hJ))
        (ne_zero_of_dvd_ne_zero hI (hs L hL)) heq
  have hsmall (P : Ideal (𝓞 K)) (hP : P ∈ a.support) :
      (a P : ℝ) + 1 ≤ c * ((P.absNorm : ℝ) ^ δ) ^ a P := by
    have he := (a P).cast_le_pow_div_sub hr
    have hone : (1 : ℝ) ≤ r ^ a P := one_le_pow₀ hr.le
    have hbase : r ≤ (P.absNorm : ℝ) ^ δ :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (haP P hP).2) hδ.le
    have hpow := pow_le_pow_left₀ (zero_le_one.trans hr.le) hbase (a P)
    have hbound : (a P : ℝ) + 1 ≤ c * r ^ a P := by
      dsimp [c]
      rw [div_eq_mul_inv] at he
      nlinarith
    exact hbound.trans
      (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hc))
  have hlarge (P : Ideal (𝓞 K)) (hPT : T ≤ P.absNorm) :
      (a P : ℝ) + 1 ≤ ((P.absNorm : ℝ) ^ δ) ^ a P := by
    have hpR : ((2 : ℝ) ^ δ⁻¹) ≤ P.absNorm :=
      hT.le.trans (by exact_mod_cast hPT)
    have hbase : (2 : ℝ) ≤ (P.absNorm : ℝ) ^ δ := by
      calc
        2 = ((2 : ℝ) ^ δ⁻¹) ^ δ :=
          (Real.rpow_inv_rpow (by norm_num) hδ.ne').symm
        _ ≤ (P.absNorm : ℝ) ^ δ :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hpR hδ.le
    have he : a P + 1 ≤ 2 ^ a P := by
      have := (a P).lt_two_pow_self
      omega
    have heR : (a P : ℝ) + 1 ≤ (2 : ℝ) ^ a P := by exact_mod_cast he
    exact heR.trans (pow_le_pow_left₀ (by norm_num) hbase _)
  have hprod : (s.card : ℝ) ≤
      (∏ P ∈ a.support, if P.absNorm < T then c else 1) *
        ∏ P ∈ a.support, ((P.absNorm : ℝ) ^ δ) ^ a P := by
    calc
      (s.card : ℝ) ≤ ((Finset.Iic a).card : ℝ) := by exact_mod_cast hcard
      _ = ∏ P ∈ a.support, ((a P : ℝ) + 1) := by
        rw [Finsupp.card_Iic, Nat.cast_prod]
        simp only [Nat.card_Iic, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_le_prod₀
        · intro P hP
          positivity
        · intro P hP
          by_cases hPT : P.absNorm < T
          · simpa only [if_pos hPT] using hsmall P hP
          · simpa only [if_neg hPT, one_mul] using
              hlarge P (Nat.le_of_not_gt hPT)
  have hconst : (∏ P ∈ a.support, if P.absNorm < T then c else 1) ≤ c ^ B := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    apply pow_le_pow_right₀ hc
    apply small_norm_ideal_card hd T
    intro P hP
    obtain ⟨hPa, hPT⟩ := Finset.mem_filter.mp hP
    exact ⟨(haP P hPa).1, hPT.le⟩
  have hnormprod : (∏ P ∈ a.support, (P.absNorm : ℝ) ^ a P) = I.absNorm := by
    have h := congrArg Ideal.absNorm (ideal_factorization_prod I hI)
    simp only [Finsupp.prod, map_prod, map_pow] at h
    exact_mod_cast h
  have hpower : (∏ P ∈ a.support, ((P.absNorm : ℝ) ^ δ) ^ a P) =
      (I.absNorm : ℝ) ^ δ := by
    calc
      _ = ∏ P ∈ a.support, ((P.absNorm : ℝ) ^ a P) ^ δ := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg P.absNorm),
          mul_comm δ (a P : ℝ), Real.rpow_natCast_mul (Nat.cast_nonneg P.absNorm)]
      _ = (∏ P ∈ a.support, (P.absNorm : ℝ) ^ a P) ^ δ :=
        Real.finsetProd_rpow a.support _
          (fun P _ => pow_nonneg (Nat.cast_nonneg P.absNorm) _) δ
      _ = _ := by rw [hnormprod]
  rw [hpower] at hprod
  exact hprod.trans
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- One finite set in `ℂ` contains every bounded-conjugate algebraic integer in
every number field of degree at most three. -/
private theorem universal_bounded_roots (B : ℝ) :
    ∃ S : Set ℂ, S.Finite ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ x : K, IsIntegral ℤ x →
      (∀ σ : K →+* ℂ, ‖σ x‖ ≤ B) → ∀ σ : K →+* ℂ, σ x ∈ S := by
  classical
  let C : ℕ := Nat.ceil (max B 1 ^ 3 * 8)
  let S : Set ℂ := ⋃ (f : Polynomial ℤ)
    (_ : f.natDegree ≤ 3 ∧ ∀ i, f.coeff i ∈ Set.Icc (-C : ℤ) C),
      ((f.map (algebraMap ℤ ℂ)).roots.toFinset : Set ℂ)
  refine ⟨S, Polynomial.bUnion_roots_finite _ 3 (Set.finite_Icc _ _), ?_⟩
  intro K _ _ hd x hx hb σ
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx
  have hdeg : (minpoly ℤ x).natDegree ≤ 3 := by
    rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact (minpoly.natDegree_le x).trans hd
  have hc (i : ℕ) : (minpoly ℤ x).coeff i ∈ Set.Icc (-C : ℤ) C := by
    rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
    have hcoeff := NumberField.Embeddings.coeff_bdd_of_norm_le hb i
    have hchoose : ((Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) : ℝ) ≤ 8 := by
      have h := (Nat.choose_le_two_pow (Module.finrank ℚ K)
        (Module.finrank ℚ K / 2)).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hd)
      exact_mod_cast h
    have hbound : max B 1 ^ Module.finrank ℚ K *
        ((Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) : ℝ) ≤
        max B 1 ^ 3 * 8 := by
      exact mul_le_mul (pow_le_pow_right₀ (le_max_right B 1) hd) hchoose
        (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_right B 1)) _)
    refine (Eq.trans_le ?_ hcoeff).trans (hbound.trans (Nat.le_ceil _))
    rw [hmap, Polynomial.coeff_map, eq_intCast, Int.norm_cast_rat,
      Int.norm_eq_abs, Int.cast_abs]
  simp only [S, Set.mem_iUnion]
  refine ⟨minpoly ℤ x, ⟨hdeg, hc⟩, ?_⟩
  change σ x ∈ (minpoly ℤ x).rootSet ℂ
  exact Polynomial.mem_rootSet.mpr
    ⟨minpoly.ne_zero hx, minpoly.aeval_algHom ℤ (σ.toIntAlgHom) x⟩

private theorem embedding_log_sum_nonneg {K : Type u} [Field K] [NumberField K]
    (x : 𝓞 K) (hx : x ≠ 0) :
    0 ≤ ∑ σ : K →+* ℂ, Real.log ‖σ (x : K)‖ := by
  classical
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hprod : (∏ σ : K →+* ℂ, ‖σ (x : K)‖) =
      (Algebra.norm ℤ x).natAbs := by
    have h := congr(‖$(Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K))‖).symm
    rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
      (fun f => ‖f (x : K)‖) (fun φ => ‖φ (x : K)‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
    rw [← Algebra.coe_norm_int x] at h
    simpa only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast,
      Nat.cast_natAbs, Int.cast_abs] using h
  have hnorm : (Algebra.norm ℤ x).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hx
  have hone : (1 : ℝ) ≤ (Algebra.norm ℤ x).natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnorm)
  have hlog : 0 ≤ Real.log ((Algebra.norm ℤ x).natAbs : ℝ) :=
    Real.log_nonneg hone
  rw [← hprod, Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr
    (fun hz => hxK (σ.injective (hz.trans (map_zero σ).symm))))] at hlog
  exact hlog

private theorem embedding_log_bounds {K : Type u} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (p : ℝ) (hp : 2 ≤ p)
    (x : 𝓞 K) (hx : x ≠ 0)
    (hb : ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18) (σ : K →+* ℂ) :
    -(36 * Real.log p) ≤ Real.log ‖σ (x : K)‖ ∧
      Real.log ‖σ (x : K)‖ ≤ 18 * Real.log p := by
  classical
  have hp0 : 0 < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hupper (φ : K →+* ℂ) : Real.log ‖φ (x : K)‖ ≤ 18 * Real.log p := by
    have hpos : 0 < ‖φ (x : K)‖ := norm_pos_iff.mpr
      (fun hz => hxK (φ.injective (hz.trans (map_zero φ).symm)))
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hpos (hb φ)
  refine ⟨?_, hupper σ⟩
  have hsum := embedding_log_sum_nonneg x hx
  have herase : (∑ φ ∈ (Finset.univ.erase σ), Real.log ‖φ (x : K)‖) ≤
      36 * Real.log p := by
    calc
      _ ≤ ∑ _φ ∈ (Finset.univ.erase σ), (18 * Real.log p) :=
        Finset.sum_le_sum (fun φ _ => hupper φ)
      _ = ((Finset.univ.erase σ).card : ℝ) * (18 * Real.log p) := by simp
      _ ≤ 2 * (18 * Real.log p) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard : (Finset.univ.erase σ).card ≤ 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            NumberField.Embeddings.card]
          omega
        exact_mod_cast hcard
      _ = _ := by ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)] at hsum
  linarith

private noncomputable def logBox {K : Type u} [Field K] [NumberField K] (p : ℝ) (x : 𝓞 K) :
    (K →+* ℂ) → ℕ :=
  fun σ => ⌊Real.log ‖σ (x : K)‖ + 36 * Real.log p⌋₊

private theorem logBox_mem {K : Type u} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (p : ℝ) (hp : 2 ≤ p)
    (x : 𝓞 K) (hx : x ≠ 0)
    (hb : ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18) :
    logBox p x ∈ @Fintype.piFinset (K →+* ℂ)
      (Classical.decEq _) inferInstance (fun _ => ℕ)
      (fun _ : K →+* ℂ => Finset.range (⌊54 * Real.log p⌋₊ + 1)) := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro σ
  rw [Finset.mem_range, Nat.lt_add_one_iff]
  apply Nat.floor_mono
  have := (embedding_log_bounds hd p hp x hx hb σ).2
  linarith

private theorem ratio_integral_of_span_eq {K : Type u} [Field K] [NumberField K]
    (x y : 𝓞 K) (hy : y ≠ 0)
    (h : Ideal.span ({y} : Set (𝓞 K)) = Ideal.span ({x} : Set (𝓞 K))) :
    IsIntegral ℤ ((x : K) / (y : K)) := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have hyK : (y : K) ≠ 0 := by exact_mod_cast hy
  have hratio : (x : K) / (y : K) = ((u : 𝓞 K) : K) := by
    apply (div_eq_iff hyK).mpr
    have hcast := congrArg (fun z : 𝓞 K => (z : K)) hu
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, mul_comm] using hcast.symm
  rw [hratio]
  exact RingOfIntegers.isIntegral_coe _

private theorem ratio_norm_le_of_logBox_eq {K : Type u} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (p : ℝ) (hp : 2 ≤ p)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hbx : ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18)
    (hby : ∀ σ : K →+* ℂ, ‖σ (y : K)‖ ≤ p ^ 18)
    (hbox : logBox p x = logBox p y) (σ : K →+* ℂ) :
    ‖σ ((x : K) / (y : K))‖ ≤ Real.exp 1 := by
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hyK : (y : K) ≠ 0 := by exact_mod_cast hy
  have hxpos : 0 < ‖σ (x : K)‖ := norm_pos_iff.mpr
    (fun hz => hxK (σ.injective (hz.trans (map_zero σ).symm)))
  have hypos : 0 < ‖σ (y : K)‖ := norm_pos_iff.mpr
    (fun hz => hyK (σ.injective (hz.trans (map_zero σ).symm)))
  have hfx := Nat.lt_floor_add_one
    (Real.log ‖σ (x : K)‖ + 36 * Real.log p)
  have hfy := Nat.floor_le
    (show 0 ≤ Real.log ‖σ (y : K)‖ + 36 * Real.log p by
      have := (embedding_log_bounds hd p hp y hy hby σ).1
      linarith)
  have hfl : ⌊Real.log ‖σ (x : K)‖ + 36 * Real.log p⌋₊ =
      ⌊Real.log ‖σ (y : K)‖ + 36 * Real.log p⌋₊ := congrFun hbox σ
  rw [hfl] at hfx
  have hdiff : Real.log ‖σ (x : K)‖ - Real.log ‖σ (y : K)‖ < 1 := by
    linarith
  rw [map_div₀, norm_div]
  apply (Real.log_lt_iff_lt_exp (div_pos hxpos hypos)).mp
    (by simpa only [Real.log_div hxpos.ne' hypos.ne'] using hdiff) |>.le

private theorem logBox_span_fiber_card {S : Set ℂ} (hS : S.Finite)
    (hroot : ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ x : K, IsIntegral ℤ x →
      (∀ σ : K →+* ℂ, ‖σ x‖ ≤ Real.exp 1) → ∀ σ : K →+* ℂ, σ x ∈ S)
    {K : Type u} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (p : ℝ) (hp : 2 ≤ p)
    (s : Finset (𝓞 K)) (hn : ∀ x ∈ s, x ≠ 0)
    (hb : ∀ x ∈ s, ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18)
    (J : Ideal (𝓞 K)) (v : (K →+* ℂ) → ℕ) :
    (s.filter (fun x => (Ideal.span ({x} : Set (𝓞 K)), logBox p x) = (J, v))).card ≤
      hS.toFinset.card := by
  classical
  let t := s.filter (fun x =>
    (Ideal.span ({x} : Set (𝓞 K)), logBox p x) = (J, v))
  by_cases ht : t.Nonempty
  · obtain ⟨y, hy⟩ := ht
    have hys := (Finset.mem_filter.mp hy).1
    have hylabels := (Finset.mem_filter.mp hy).2
    let σ₀ : K →+* ℂ := Classical.choice inferInstance
    apply Finset.card_le_card_of_injOn
      (fun x : 𝓞 K => σ₀ ((x : K) / (y : K)))
    · intro x hx
      obtain ⟨hxs, hxlabels⟩ := Finset.mem_filter.mp hx
      apply hS.mem_toFinset.mpr
      apply hroot K hd _
      · apply ratio_integral_of_span_eq x y (hn y hys)
        exact (Prod.mk.inj hylabels).1.trans (Prod.mk.inj hxlabels).1.symm
      · intro σ
        apply ratio_norm_le_of_logBox_eq hd p hp x y (hn x hxs) (hn y hys)
          (hb x hxs) (hb y hys)
        exact (Prod.mk.inj hxlabels).2.trans (Prod.mk.inj hylabels).2.symm
    · intro x hx z hz hxz
      have hyK : (y : K) ≠ 0 := by exact_mod_cast hn y hys
      apply RingOfIntegers.ext
      exact (div_left_inj' hyK).mp (σ₀.injective hxz)
  · have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change t.card ≤ hS.toFinset.card
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

/-- A bounded-conjugate divisor count before the final absorption of the
logarithmic factor. Its universal integer constant is independent of the field. -/
private theorem bounded_divisors_log_bound :
    ∃ M : ℕ, 0 < M ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ (p : ℝ), 2 ≤ p →
      ∀ (D : 𝓞 K), D ≠ 0 → ∀ s : Finset (𝓞 K),
      (∀ x ∈ s, x ∣ D) →
      (∀ x ∈ s, ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18) →
      s.card ≤ M * (⌊54 * Real.log p⌋₊ + 1) ^ 3 *
        (s.image (fun x => Ideal.span ({x} : Set (𝓞 K)))).card := by
  classical
  obtain ⟨S, hS, hroot⟩ := universal_bounded_roots (Real.exp 1)
  refine ⟨hS.toFinset.card + 1, Nat.zero_lt_succ _, ?_⟩
  intro K _ _ hd p hp D hD s hs hb
  have hn (x : 𝓞 K) (hx : x ∈ s) : x ≠ 0 :=
    ne_zero_of_dvd_ne_zero hD (hs x hx)
  let js := s.image (fun x => Ideal.span ({x} : Set (𝓞 K)))
  let vs := Fintype.piFinset
    (fun _ : K →+* ℂ => Finset.range (⌊54 * Real.log p⌋₊ + 1))
  have hmaps : ∀ x ∈ s,
      (Ideal.span ({x} : Set (𝓞 K)), logBox p x) ∈ js ×ˢ vs := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      logBox_mem hd p hp x (hn x hx) (hb x hx)⟩
  have hcount : s.card ≤ hS.toFinset.card * (js ×ˢ vs).card := by
    apply Finset.card_le_mul_card_image_of_maps_to hmaps hS.toFinset.card
    rintro ⟨J, v⟩ _
    exact logBox_span_fiber_card hS hroot hd p hp s hn hb J v
  have hv : vs.card ≤ (⌊54 * Real.log p⌋₊ + 1) ^ 3 := by
    dsimp [vs]
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ,
      NumberField.Embeddings.card]
    exact Nat.pow_le_pow_right (by omega) hd
  calc
    s.card ≤ hS.toFinset.card * (js.card * vs.card) := by
      simpa only [Finset.card_product] using hcount
    _ ≤ (hS.toFinset.card + 1) * js.card * (⌊54 * Real.log p⌋₊ + 1) ^ 3 := by
      calc
        _ ≤ (hS.toFinset.card + 1) * (js.card * vs.card) :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ ≤ _ := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hv)
    _ = _ := by ring

/-- Uniform bounded-conjugate divisor estimate. The constant is chosen before
the field, and depends only on the positive exponent. -/
theorem bounded_divisors_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ (p : ℝ), 2 ≤ p →
      ∀ (D : 𝓞 K), D ≠ 0 → ((Algebra.norm ℤ D).natAbs : ℝ) ≤ p ^ 108 →
      ∀ s : Finset (𝓞 K), (∀ x ∈ s, x ∣ D) →
      (∀ x ∈ s, ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ p ^ 18) →
      (s.card : ℝ) ≤ C * p ^ ε := by
  classical
  let δ : ℝ := ε / 216
  let γ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨A, hA, hideals⟩ := ideal_divisors_subpower δ hδ
  obtain ⟨M, hM, hlogcount⟩ := bounded_divisors_log_bound
  let L : ℝ := 54 / γ + 2
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨(M : ℝ) * A * L ^ 3, by positivity, ?_⟩
  intro K _ _ hd p hp D hD hnorm s hs hb
  let js := s.image (fun x => Ideal.span ({x} : Set (𝓞 K)))
  have hDspan : Ideal.span ({D} : Set (𝓞 K)) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hD
  have hjs : ∀ J ∈ js, J ∣ Ideal.span ({D} : Set (𝓞 K)) := by
    intro J hJ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
    exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (hs x hx)
  have hid : (js.card : ℝ) ≤ A * (((Algebra.norm ℤ D).natAbs : ℝ) ^ δ) := by
    simpa only [Ideal.absNorm_span_singleton] using
      hideals K hd (Ideal.span ({D} : Set (𝓞 K))) hDspan js hjs
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpn : 0 ≤ p := hp0.le
  have hnormpow : (((Algebra.norm ℤ D).natAbs : ℝ) ^ δ) ≤ p ^ (ε / 2) := by
    calc
      _ ≤ (p ^ 108) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le
      _ = p ^ ((108 : ℝ) * δ) :=
        (Real.rpow_natCast_mul hpn 108 δ).symm
      _ = _ := by congr 1; dsimp [δ]; ring
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlogs : ((⌊54 * Real.log p⌋₊ + 1 : ℕ) : ℝ) ≤ L * p ^ γ := by
    have hf := Nat.floor_le (show 0 ≤ 54 * Real.log p by positivity)
    have hl := Real.log_le_rpow_div hpn hγ
    have hpγ : 1 ≤ p ^ γ := Real.one_le_rpow hp1 hγ.le
    calc
      _ ≤ 54 * Real.log p + 2 := by push_cast; linarith
      _ ≤ 54 * (p ^ γ / γ) + 2 := by linarith
      _ ≤ 54 * (p ^ γ / γ) + 2 * p ^ γ := by linarith
      _ = L * p ^ γ := by dsimp [L]; ring
  have hlogcube : (((⌊54 * Real.log p⌋₊ + 1 : ℕ) : ℝ) ^ 3) ≤
      L ^ 3 * p ^ (ε / 2) := by
    calc
      _ ≤ (L * p ^ γ) ^ 3 := pow_le_pow_left₀ (by positivity) hlogs 3
      _ = L ^ 3 * (p ^ γ) ^ 3 := mul_pow _ _ _
      _ = L ^ 3 * p ^ (γ * 3) := by
        rw [← Real.rpow_mul_natCast hpn γ 3]
        norm_num
      _ = _ := by congr 2; dsimp [γ]; ring
  have hc : (s.card : ℝ) ≤ (M : ℝ) *
      (((⌊54 * Real.log p⌋₊ + 1 : ℕ) : ℝ) ^ 3) * (js.card : ℝ) := by
    exact_mod_cast hlogcount K hd p hp D hD s hs hb
  calc
    (s.card : ℝ) ≤ (M : ℝ) *
        (((⌊54 * Real.log p⌋₊ + 1 : ℕ) : ℝ) ^ 3) * (js.card : ℝ) := hc
    _ ≤ (M : ℝ) * (L ^ 3 * p ^ (ε / 2)) * (A * p ^ (ε / 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlogcube (Nat.cast_nonneg M)
      · exact hid.trans (mul_le_mul_of_nonneg_left hnormpow hA.le)
      · exact Nat.cast_nonneg _
      · positivity
    _ = ((M : ℝ) * A * L ^ 3) * p ^ ε := by
      have hpow : p ^ (ε / 2) * p ^ (ε / 2) = p ^ ε := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      calc
        _ = ((M : ℝ) * A * L ^ 3) *
            (p ^ (ε / 2) * p ^ (ε / 2)) := by ring
        _ = _ := by rw [hpow]

/-- Fixed nonzero products determine the second member from the first, so the
same uniform estimate counts actual pairs of algebraic integer values. -/
theorem fixed_product_pairs_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ 3 → ∀ (p : ℝ), 2 ≤ p →
      ∀ (D : 𝓞 K), D ≠ 0 → ((Algebra.norm ℤ D).natAbs : ℝ) ≤ p ^ 108 →
      ∀ s : Finset ((𝓞 K) × (𝓞 K)),
      (∀ z ∈ s, z.1 * z.2 = D) →
      (∀ z ∈ s, ∀ σ : K →+* ℂ, ‖σ (z.1 : K)‖ ≤ p ^ 18) →
      (s.card : ℝ) ≤ C * p ^ ε := by
  classical
  obtain ⟨C, hC, h⟩ := bounded_divisors_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro K _ _ hd p hp D hD hnorm s hs hb
  have hproj : Set.InjOn (Prod.fst : (𝓞 K) × (𝓞 K) → 𝓞 K) (s : Set _) := by
    intro x hx y hy hxy
    have hx0 : x.1 ≠ 0 := by
      intro hz
      exact hD (by simpa only [hz, zero_mul] using (hs x hx).symm)
    apply Prod.ext hxy
    apply mul_left_cancel₀ hx0
    simpa only [hxy] using (hs x hx).trans (hs y hy).symm
  have hc := h K hd p hp D hD hnorm (s.image Prod.fst) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨z.2, (hs z hz).symm⟩) (by
    intro x hx σ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hb z hz σ)
  simpa only [Finset.card_image_of_injOn hproj] using hc

end D5.S3.Arith.Divisors.NumberFieldDivisorSubpower
