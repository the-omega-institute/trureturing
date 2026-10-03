/- GID: D5/S3/Arith/DiophantineApproximation/ThueEquation
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/ThueEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nonzero fiber of a binary form with three projective roots is finite. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.BinaryForm
public import D5.S3.Arith.DiophantineApproximation.RothTheorem
public import D5.S3.Arith.DiophantineApproximation.RationalPlaces
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

@[expose] public section

open Polynomial Height NumberField IntermediateField Filter
open scoped ENNReal NNReal

theorem Real.finite_setOf_pow_abs_sub_div_mul_pow_le {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    (hirr : Irrational ξ) {μ e : ℕ} (hμ : 0 < μ) (he : 2 * μ < e) (C : ℝ) :
    {z : ℤ × ℤ | z.2 ≠ 0 ∧ |ξ - (z.1 : ℝ) / z.2| ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
  have hImported1 {m : ℤ} {n : ℕ} (hn : 0 < n) :
      max (((m : ℚ) / (n : ℚ)).num.natAbs) (((m : ℚ) / (n : ℚ)).den) ≤ max m.natAbs n := by
    have hn0 : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn.ne'
    have hdiv : ((m : ℚ) / ((n : ℤ) : ℚ)) = Rat.divInt m (n : ℤ) := (Rat.divInt_eq_div m n).symm
    have hden : (((m : ℚ) / (n : ℚ)).den) ≤ n := by
      have h := Rat.den_dvd m (n : ℤ)
      rw [← hdiv] at h
      push_cast at h ⊢
      have h' : (((m : ℚ) / (n : ℚ)).den) ∣ n := by
        rwa [Int.natCast_dvd_natCast] at h
      exact Nat.le_of_dvd hn h'
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [Int.cast_zero, zero_div, Rat.num_zero, Int.natAbs_zero, Rat.den_zero,
        Int.natAbs_zero]
      exact le_trans (max_le (Nat.zero_le _) hn) (le_max_right _ _)
    · have hnum : (((m : ℚ) / (n : ℚ)).num) ∣ m := by
        have h := Rat.num_dvd m hn0
        rw [← hdiv] at h
        push_cast at h ⊢
        exact h
      have hnum' : (((m : ℚ) / (n : ℚ)).num.natAbs) ≤ m.natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.natAbs_dvd_natAbs.mpr hnum)
      exact max_le_max hnum' hden
  have hImported2 (X Y : ℝ) :
      {z : ℤ × ℤ | |(z.1 : ℝ)| ≤ X ∧ |(z.2 : ℝ)| ≤ Y}.Finite := by
    refine ((Set.finite_Icc (-⌈X⌉) ⌈X⌉).prod (Set.finite_Icc (-⌈Y⌉) ⌈Y⌉)).subset ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    have hx' : |x| ≤ ⌈X⌉ := by
      have : ((|x| : ℤ) : ℝ) ≤ ⌈X⌉ := by rw [Int.cast_abs]; exact hx.trans (Int.le_ceil X)
      exact_mod_cast this
    have hy' : |y| ≤ ⌈Y⌉ := by
      have : ((|y| : ℤ) : ℝ) ≤ ⌈Y⌉ := by rw [Int.cast_abs]; exact hy.trans (Int.le_ceil Y)
      exact_mod_cast this
    exact ⟨abs_le.mp hx', abs_le.mp hy'⟩
  have hImported3 {x y : ℤ} (hy : y ≠ 0) :
      max ((x : ℚ) / y).num.natAbs ((x : ℚ) / y).den ≤ max x.natAbs y.natAbs := by
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have hq : (x : ℚ) / y = ((-x : ℤ) : ℚ) / ((y.natAbs : ℕ) : ℚ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
        push_cast
        rw [neg_div_neg_eq]
      rw [hq]
      have := hImported1 (m := -x) (Int.natAbs_pos.mpr hy)
      rwa [Int.natAbs_neg] at this
    · have hq : (x : ℚ) / y = (x : ℚ) / ((y.natAbs : ℕ) : ℚ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
      rw [hq]
      exact hImported1 (Int.natAbs_pos.mpr hy)
  have hImported4 {y : ℤ} (hy : y ≠ 0) : (1 : ℝ) ≤ |(y : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hy
  have hImported5 {t K : ℝ} {μ : ℕ} (hμ : μ ≠ 0) (h : t ^ μ ≤ K) :
      t ≤ max 1 K := by
    by_contra hcon
    push Not at hcon
    have h1 : 1 < t := (le_max_left _ _).trans_lt hcon
    have : t ≤ t ^ μ := le_self_pow₀ h1.le hμ
    linarith [le_max_right 1 K]
  have hImported6 {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) {κ : ℝ} (hκ : 2 < κ) :
      {β : ℚ | min 1 |ξ - (β : ℝ)| ≤ (max β.num.natAbs β.den : ℝ) ^ (-κ)}.Finite := by
    have hint : IsIntegral ℚ ξ := hξ.isIntegral
    have : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
    have : NumberField ℚ⟮ξ⟯ := {}
    set w : AbsoluteValue ℚ⟮ξ⟯ ℝ := AbsoluteValue.abs.comp (algebraMap ℚ⟮ξ⟯ ℝ).injective with hwdef
    have hwapply : ∀ x : ℚ⟮ξ⟯, w x = |(algebraMap ℚ⟮ξ⟯ ℝ) x| := fun x ↦ rfl
    have hw : w.LiesOver (Rat.infinitePlace.1) := by
      refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
      change w (algebraMap ℚ ℚ⟮ξ⟯ q) = Rat.infinitePlace.1 q
      rw [hwapply, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ,
        ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
      simp
    set a : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hadef
    have ha : (algebraMap ℚ⟮ξ⟯ ℝ) a = ξ := rfl
    have hroth := finite_setOf_prod_min_one_le (K := ℚ) (F := ℚ⟮ξ⟯) {Rat.infinitePlace} ∅
      (fun _ ↦ w) (fun v hv ↦ by rwa [Finset.mem_singleton.mp hv])
      (fun v hv ↦ absurd hv (Finset.notMem_empty v)) (fun _ ↦ a) hκ
    refine hroth.subset fun β hβ ↦ ?_
    rw [Set.mem_ofPred_eq] at hβ ⊢
    rw [Finset.prod_singleton, Finset.prod_empty, mul_one,
      NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
      Rat.mulHeight₁_eq_max, Nat.cast_max]
    have hval : w ((algebraMap ℚ ℚ⟮ξ⟯) β - a) = |ξ - (β : ℝ)| := by
      rw [hwapply, map_sub, ha, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ, abs_sub_comm]
      simp
    rw [hval]
    exact hβ
  set K : ℝ := max 1 C with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hCK : C ≤ K := le_max_right _ _
  set A : ℝ := |ξ| + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg ξ]
  set Y₁ : ℝ := max K (K ^ 2 * A ^ (4 * μ + 1)) with hY₁
  set κ : ℝ := 2 + 1 / (2 * μ) with hκdef
  have hμR : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hκ : 2 < κ := by rw [hκdef]; linarith [show (0 : ℝ) < 1 / (2 * μ) by positivity]
  have hκμ : κ * ((2 * μ : ℕ) : ℝ) = ((4 * μ + 1 : ℕ) : ℝ) := by
    rw [hκdef]; push_cast; field_simp; ring
  have hroth := hImported6 hξ hκ
  -- the fibre over a single rational is finite
  have hfib : ∀ β : ℚ, {z : ℤ × ℤ | z.2 ≠ 0 ∧ ((z.1 : ℚ) / z.2 = β) ∧
      |ξ - (z.1 : ℝ) / z.2| ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
    intro β
    have hD : 0 < |ξ - (β : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hirr ⟨β, h.symm⟩)
    refine (hImported2 (|(β : ℝ)| * (C / |ξ - (β : ℝ)| ^ μ))
      (C / |ξ - (β : ℝ)| ^ μ)).subset ?_
    rintro ⟨x, y⟩ ⟨hy, hxy, hle⟩
    have hxyR : (x : ℝ) / y = β := by rw [← hxy]; push_cast; rfl
    rw [hxyR] at hle
    have hy1 := hImported4 hy
    have hyC : |(y : ℝ)| ≤ C / |ξ - (β : ℝ)| ^ μ := by
      rw [le_div_iff₀ (pow_pos hD μ), mul_comm]
      refine le_trans ?_ hle
      gcongr
      exact le_self_pow₀ hy1 (by omega)
    refine ⟨?_, hyC⟩
    have hx : (x : ℝ) = β * y := by
      rw [← hxyR]; field_simp
    rw [hx, abs_mul]
    gcongr
  refine ((hImported2 ((|ξ| + K) * Y₁) Y₁).union
    (hroth.biUnion fun β _ ↦ hfib β)).subset ?_
  rintro ⟨x, y⟩ ⟨hy, hle⟩
  change y ≠ 0 at hy
  change |ξ - (x : ℝ) / y| ^ μ * |(y : ℝ)| ^ e ≤ C at hle
  have hy1 := hImported4 hy
  set D := |ξ - (x : ℝ) / y| with hDdef
  have hD0 : 0 ≤ D := abs_nonneg _
  have hleK : D ^ μ * |(y : ℝ)| ^ e ≤ K := hle.trans hCK
  -- first, `|x| ≤ (|ξ| + L) |y|` as soon as `D ≤ L`
  have hxA : ∀ L : ℝ, D ≤ L → |(x : ℝ)| ≤ (|ξ| + L) * |(y : ℝ)| := by
    intro L hDL
    have : |(x : ℝ) / y| ≤ |ξ| + L := by
      have := abs_sub_abs_le_abs_sub ((x : ℝ) / y) ξ
      rw [abs_sub_comm] at this
      linarith
    rwa [abs_div, div_le_iff₀ (by linarith)] at this
  by_cases hsmall : |(y : ℝ)| ≤ Y₁
  · left
    have hDK : D ≤ K := by
      refine (hImported5 (μ := μ) (by omega) ?_).trans (max_le hK1 le_rfl)
      refine le_trans ?_ hleK
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hy1)
    refine ⟨(hxA K hDK).trans ?_, hsmall⟩
    exact mul_le_mul_of_nonneg_left hsmall (by linarith [abs_nonneg ξ])
  right
  push Not at hsmall
  have hYK : K ≤ Y₁ := le_max_left _ _
  have hY2 : K ^ 2 * A ^ (4 * μ + 1) ≤ Y₁ := le_max_right _ _
  have hD1 : D ≤ 1 := by
    by_contra hD1
    push Not at hD1
    have h1 : 1 ≤ D ^ μ := one_le_pow₀ hD1.le
    have h2 : |(y : ℝ)| ≤ |(y : ℝ)| ^ e := le_self_pow₀ hy1 (by omega)
    have h3 : |(y : ℝ)| ^ e ≤ D ^ μ * |(y : ℝ)| ^ e := le_mul_of_one_le_left (by positivity) h1
    linarith
  set β : ℚ := (x : ℚ) / y with hβ
  have hβR : (β : ℝ) = (x : ℝ) / y := by rw [hβ]; push_cast; rfl
  refine Set.mem_iUnion₂.mpr ⟨β, ?_, hy, rfl, hle⟩
  rw [Set.mem_ofPred_eq, hβR]
  set H : ℝ := max (β.num.natAbs : ℝ) (β.den : ℝ) with hHdef
  have hH1 : 1 ≤ H := le_max_of_le_right (by exact_mod_cast β.pos)
  have hH0 : 0 ≤ H := by linarith
  have hHle : H ≤ A * |(y : ℝ)| := by
    have h := (Nat.cast_le (α := ℝ)).mpr (hImported3 (x := x) hy)
    rw [Nat.cast_max, Nat.cast_max] at h
    refine h.trans (max_le ?_ ?_)
    · rw [Nat.cast_natAbs, Int.cast_abs]
      exact hxA 1 hD1
    · rw [Nat.cast_natAbs, Int.cast_abs]
      exact le_mul_of_one_le_left (abs_nonneg _) hA1
  refine (min_le_right _ _).trans ?_
  refine le_of_pow_le_pow_left₀ (n := 2 * μ) (by omega) (Real.rpow_nonneg hH0 _) ?_
  rw [← Real.rpow_mul_natCast hH0, neg_mul, hκμ, Real.rpow_neg hH0, Real.rpow_natCast,
    ← one_div, le_div_iff₀ (by positivity)]
  have hsq : (D ^ μ) ^ 2 * |(y : ℝ)| ^ (2 * e) ≤ K ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hleK 2
    rwa [mul_pow, ← pow_mul |(y : ℝ)|, mul_comm e 2] at this
  have hy2e : |(y : ℝ)| ^ (4 * μ + 1) * |(y : ℝ)| ≤ |(y : ℝ)| ^ (2 * e) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hy1 (by omega)
  have hpos : 0 < |(y : ℝ)| := by linarith
  have key : D ^ (2 * μ) * H ^ (4 * μ + 1) * |(y : ℝ)| ≤ 1 * |(y : ℝ)| := by
    calc D ^ (2 * μ) * H ^ (4 * μ + 1) * |(y : ℝ)|
        ≤ (D ^ μ) ^ 2 * (A * |(y : ℝ)|) ^ (4 * μ + 1) * |(y : ℝ)| := by
          rw [← pow_mul, mul_comm μ 2]; gcongr
      _ = ((D ^ μ) ^ 2 * (|(y : ℝ)| ^ (4 * μ + 1) * |(y : ℝ)|)) * A ^ (4 * μ + 1) := by
          rw [mul_pow]; ring
      _ ≤ ((D ^ μ) ^ 2 * |(y : ℝ)| ^ (2 * e)) * A ^ (4 * μ + 1) := by gcongr
      _ ≤ K ^ 2 * A ^ (4 * μ + 1) := by gcongr
      _ ≤ 1 * |(y : ℝ)| := by linarith
  exact le_of_mul_le_mul_right key hpos

theorem Complex.finite_setOf_norm_div_sub_pow_mul_pow_le {r : ℂ} (hr : IsAlgebraic ℚ r)
    {μ e : ℕ} (hμ : 0 < μ) (he : μ < e)
    (hirr : ∀ ξ : ℝ, (ξ : ℂ) = r → Irrational ξ → 2 * μ < e) (C : ℝ) :
    {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
  have hImported2 (X Y : ℝ) :
      {z : ℤ × ℤ | |(z.1 : ℝ)| ≤ X ∧ |(z.2 : ℝ)| ≤ Y}.Finite := by
    refine ((Set.finite_Icc (-⌈X⌉) ⌈X⌉).prod (Set.finite_Icc (-⌈Y⌉) ⌈Y⌉)).subset ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    have hx' : |x| ≤ ⌈X⌉ := by
      have : ((|x| : ℤ) : ℝ) ≤ ⌈X⌉ := by rw [Int.cast_abs]; exact hx.trans (Int.le_ceil X)
      exact_mod_cast this
    have hy' : |y| ≤ ⌈Y⌉ := by
      have : ((|y| : ℤ) : ℝ) ≤ ⌈Y⌉ := by rw [Int.cast_abs]; exact hy.trans (Int.le_ceil Y)
      exact_mod_cast this
    exact ⟨abs_le.mp hx', abs_le.mp hy'⟩
  have hImported4 {y : ℤ} (hy : y ≠ 0) : (1 : ℝ) ≤ |(y : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hy
  have hImported5 {t K : ℝ} {μ : ℕ} (hμ : μ ≠ 0) (h : t ^ μ ≤ K) :
      t ≤ max 1 K := by
    by_contra hcon
    push Not at hcon
    have h1 : 1 < t := (le_max_left _ _).trans_lt hcon
    have : t ≤ t ^ μ := le_self_pow₀ h1.le hμ
    linarith [le_max_right 1 K]
  -- the bound on `x` in terms of `y`, common to the two elementary cases
  have hxB : ∀ z ∈ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C},
      |(z.1 : ℝ)| ≤ (‖r‖ + max 1 C) * |(z.2 : ℝ)| := by
    rintro ⟨x, y⟩ ⟨hy, -, hle⟩
    change y ≠ 0 at hy
    change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
    have hy1 := hImported4 hy
    have h1 : ‖(x : ℂ) / y - r‖ ≤ max 1 C := by
      refine hImported5 (μ := μ) (by omega) (le_trans ?_ hle)
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hy1)
    have h2 : ‖(x : ℂ) / y‖ ≤ ‖r‖ + max 1 C := by
      have := norm_sub_norm_le ((x : ℂ) / y) r
      linarith
    have h3 : ‖(x : ℂ) / y‖ = |(x : ℝ)| / |(y : ℝ)| := by
      rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
    rw [h3, div_le_iff₀ (by linarith)] at h2
    exact h2
  have hbox : ∀ Y : ℝ, (∀ z ∈ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
      ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}, |(z.2 : ℝ)| ≤ Y) →
      {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
        ‖(z.1 : ℂ) / z.2 - r‖ ^ μ * |(z.2 : ℝ)| ^ e ≤ C}.Finite := by
    intro Y hY
    refine (hImported2 ((‖r‖ + max 1 C) * Y) Y).subset fun z hz ↦ ⟨?_, hY z hz⟩
    refine (hxB z hz).trans (mul_le_mul_of_nonneg_left (hY z hz) ?_)
    have := le_max_left 1 C
    positivity
  by_cases him : r.im = 0
  · set ξ : ℝ := r.re with hξdef
    have hrξ : (ξ : ℂ) = r := Complex.ext (by simp [hξdef]) (by simp [him])
    have hnorm : ∀ x y : ℤ, ‖(x : ℂ) / y - r‖ = |ξ - (x : ℝ) / y| := by
      intro x y
      rw [← hrξ, abs_sub_comm, show (x : ℂ) / y - ξ = (((x : ℝ) / y - ξ : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
    by_cases hirrξ : Irrational ξ
    · -- Roth
      have hξalg : IsAlgebraic ℚ ξ := by
        obtain ⟨p, hp0, hp⟩ := hr
        refine ⟨p, hp0, ?_⟩
        rw [← hrξ] at hp
        have : (algebraMap ℝ ℂ) (Polynomial.aeval ξ p) = 0 := by
          rw [← Polynomial.aeval_algebraMap_apply]
          exact hp
        exact (algebraMap ℝ ℂ).injective (this.trans (map_zero _).symm)
      refine (Real.finite_setOf_pow_abs_sub_div_mul_pow_le hξalg hirrξ hμ
        (hirr ξ hrξ hirrξ) C).subset ?_
      rintro ⟨x, y⟩ ⟨hy, -, hle⟩
      refine ⟨hy, ?_⟩
      change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
      rwa [hnorm] at hle
    · -- a rational root: Liouville with exponent one
      obtain ⟨c, hc⟩ : ∃ c : ℚ, (c : ℝ) = ξ := by
        by_contra hcon
        exact hirrξ fun ⟨c, hc'⟩ ↦ hcon ⟨c, hc'⟩
      refine hbox (max 1 C * (c.den : ℝ) ^ μ) ?_
      rintro ⟨x, y⟩ ⟨hy, hne, hle⟩
      change y ≠ 0 at hy
      change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
      change (x : ℂ) / y ≠ r at hne
      rw [hnorm] at hle
      change |(y : ℝ)| ≤ max 1 C * (c.den : ℝ) ^ μ
      have hy1 := hImported4 hy
      have hden : (0 : ℝ) < c.den := by exact_mod_cast c.pos
      set N : ℤ := c.num * y - x * c.den with hN
      have hN0 : N ≠ 0 := by
        intro h0
        apply hne
        rw [← hrξ, ← hc]
        have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
        have hdC : ((c.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast c.den_nz
        have h' : x * (c.den : ℤ) = c.num * y := by rw [hN] at h0; linarith
        rw [Complex.ofReal_ratCast, Rat.cast_def, ← Int.cast_natCast, div_eq_div_iff hyC hdC]
        exact_mod_cast h'
      have hid : |ξ - (x : ℝ) / y| * |(y : ℝ)| = |(N : ℝ)| / c.den := by
        have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
        have : ((c : ℝ) - (x : ℝ) / y) * y = (N : ℝ) / c.den := by
          rw [Rat.cast_def, hN]
          push_cast
          field_simp
        rw [← hc, ← abs_mul, this, abs_div, Nat.abs_cast]
      have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := hImported4 hN0
      have hlow : (1 / (c.den : ℝ)) ^ μ * |(y : ℝ)| ≤ C := by
        refine le_trans ?_ hle
        have hsplit : |ξ - (x : ℝ) / y| ^ μ * |(y : ℝ)| ^ e =
            (|ξ - (x : ℝ) / y| * |(y : ℝ)|) ^ μ * |(y : ℝ)| ^ (e - μ) := by
          rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' he.le]
        rw [hsplit, hid]
        gcongr
        exact le_self_pow₀ hy1 (by omega)
      rw [div_pow, one_pow, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)] at hlow
      exact hlow.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · -- a non-real root: `x / y` stays `|Im r|` away from it
    have himpos : 0 < |r.im| := abs_pos.mpr him
    refine hbox (C / |r.im| ^ μ) ?_
    rintro ⟨x, y⟩ ⟨hy, -, hle⟩
    change y ≠ 0 at hy
    change ‖(x : ℂ) / y - r‖ ^ μ * |(y : ℝ)| ^ e ≤ C at hle
    change |(y : ℝ)| ≤ C / |r.im| ^ μ
    have hy1 := hImported4 hy
    have hfar : |r.im| ≤ ‖(x : ℂ) / y - r‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have : ((x : ℂ) / y - r).im = -r.im := by
        rw [Complex.sub_im]
        have : ((x : ℂ) / y).im = 0 := by
          rw [show ((x : ℂ) / y) = (((x : ℝ) / y : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
        rw [this, zero_sub]
      rw [this, abs_neg]
    rw [le_div_iff₀ (pow_pos himpos μ), mul_comm]
    refine le_trans ?_ hle
    gcongr
    exact le_self_pow₀ hy1 (by omega)

theorem Polynomial.finite_setOf_eval_homogenize_eq {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d)
    (hroots : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card +
      if g.natDegree = d then 0 else 1)
    {m : ℤ} (hm : m ≠ 0) :
    {z : ℤ × ℤ | MvPolynomial.eval ![z.1, z.2] (g.homogenize d) = m}.Finite := by
  have hImported2 (X Y : ℝ) :
      {z : ℤ × ℤ | |(z.1 : ℝ)| ≤ X ∧ |(z.2 : ℝ)| ≤ Y}.Finite := by
    refine ((Set.finite_Icc (-⌈X⌉) ⌈X⌉).prod (Set.finite_Icc (-⌈Y⌉) ⌈Y⌉)).subset ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    have hx' : |x| ≤ ⌈X⌉ := by
      have : ((|x| : ℤ) : ℝ) ≤ ⌈X⌉ := by rw [Int.cast_abs]; exact hx.trans (Int.le_ceil X)
      exact_mod_cast this
    have hy' : |y| ≤ ⌈Y⌉ := by
      have : ((|y| : ℤ) : ℝ) ≤ ⌈Y⌉ := by rw [Int.cast_abs]; exact hy.trans (Int.le_ceil Y)
      exact_mod_cast this
    exact ⟨abs_le.mp hx', abs_le.mp hy'⟩
  have hImported4 {y : ℤ} (hy : y ≠ 0) : (1 : ℝ) ≤ |(y : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hy
  have hImported5 {t K : ℝ} {μ : ℕ} (hμ : μ ≠ 0) (h : t ^ μ ≤ K) :
      t ≤ max 1 K := by
    by_contra hcon
    push Not at hcon
    have h1 : 1 < t := (le_max_left _ _).trans_lt hcon
    have : t ≤ t ^ μ := le_self_pow₀ h1.le hμ
    linarith [le_max_right 1 K]
  have hImported7 (p : ℤ[X])
      (n : ℕ) (x : ℤ) : MvPolynomial.eval ![x, 0] (p.homogenize n) = p.coeff n * x ^ n := by
    simp only [homogenize, MvPolynomial.eval_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      MvPolynomial.eval_monomial]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [Finsupp.prod_fintype, Fin.prod_univ_two]
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      simp [zero_pow (Nat.sub_ne_zero_of_lt hk)]
  have hImported8 {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d) (x y : ℤ)
      (hy : y ≠ 0) : ((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℂ) =
        (g.map (Int.castRingHom ℂ)).eval ((x : ℂ) / y) * (y : ℂ) ^ d := by
    have h1 : ((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℂ) =
        MvPolynomial.eval ![(x : ℂ), (y : ℂ)] ((g.map (Int.castRingHom ℂ)).homogenize d) := by
      have hv : (Int.castRingHom ℂ) ∘ ![x, y] = ![(x : ℂ), (y : ℂ)] := by
        ext i; fin_cases i <;> simp
      rw [homogenize_map, ← eq_intCast (Int.castRingHom ℂ), MvPolynomial.map_eval, hv]
    rw [h1, eval_homogenize (natDegree_map_le.trans hd)]
    · simp
    · simpa using hy
  have hImported9 (g : ℤ[X]) (t : ℂ) :
      (g.map (Int.castRingHom ℂ)).eval t = (g.leadingCoeff : ℂ) *
        ∏ r ∈ (g.map (Int.castRingHom ℂ)).roots.toFinset,
          (t - r) ^ (g.map (Int.castRingHom ℂ)).roots.count r := by
    classical
    set gc := g.map (Int.castRingHom ℂ) with hgc
    have hcard : Multiset.card gc.roots = gc.natDegree :=
      splits_iff_card_roots.mp (IsAlgClosed.splits gc)
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    have hlc : gc.leadingCoeff = (g.leadingCoeff : ℂ) := by
      rw [hgc, leadingCoeff_map_of_injective (RingHom.injective_int _)]
      simp
    rw [hlc]
    congr 1
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    simp
  classical
  set gc := g.map (Int.castRingHom ℂ) with hgc
  set rs := gc.roots with hrs
  set R := rs.toFinset with hR
  set n := g.natDegree with hn
  set a := g.leadingCoeff with ha
  have hg : g ≠ 0 := by
    rintro rfl
    simp only [hgc, hrs, hR, Polynomial.map_zero, roots_zero, Multiset.toFinset_zero,
      Finset.card_empty, zero_add] at hroots
    split_ifs at hroots <;> omega
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have haR : (1 : ℝ) ≤ |(a : ℝ)| := hImported4 ha0
  have hgc0 : gc ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg
  have hcard : Multiset.card rs = n := by
    rw [hrs, splits_iff_card_roots.mp (IsAlgClosed.splits gc), hgc,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  have hsum : ∑ r ∈ R, rs.count r = n := by rw [hR, Multiset.toFinset_sum_count_eq, hcard]
  have hR2 : 2 ≤ R.card := by split_ifs at hroots <;> omega
  have hcount : ∀ r ∈ R, 0 < rs.count r := fun r hr ↦ Multiset.count_pos.mpr
    (Multiset.mem_toFinset.mp hr)
  have hnR : R.card ≤ n := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun r hr ↦ hcount r hr
  -- the identity `|G(x, y)| = |a| |y| ^ d ∏ ‖x / y - r‖ ^ μ(r)`
  have hid : ∀ x y : ℤ, y ≠ 0 → |((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℝ)| =
      |(a : ℝ)| * |(y : ℝ)| ^ d * ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by
    intro x y hy
    have h1 := congrArg norm (hImported8 hd x y hy)
    rw [hImported9] at h1
    rw [Complex.norm_intCast] at h1
    rw [h1, norm_mul, norm_mul, norm_pow, Complex.norm_intCast, Complex.norm_intCast,
      Complex.norm_prod]
    simp_rw [norm_pow]
    ring
  -- a first bound: `|x| ≤ B |y|`
  set Rs : ℝ := ∑ r ∈ R, ‖r‖ with hRs
  have hxbound : ∀ x y : ℤ, y ≠ 0 → MvPolynomial.eval ![x, y] (g.homogenize d) = m →
      |(x : ℝ)| ≤ (Rs + 1 + |(m : ℝ)|) * |(y : ℝ)| := by
    intro x y hy hxy
    have hy1 := hImported4 hy
    have hidm := hid x y hy
    rw [hxy] at hidm
    have htnorm : ‖(x : ℂ) / y‖ = |(x : ℝ)| / |(y : ℝ)| := by
      rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
    suffices h : ‖(x : ℂ) / y‖ ≤ Rs + 1 + |(m : ℝ)| by
      rwa [htnorm, div_le_iff₀ (by linarith)] at h
    by_cases hsmall : ‖(x : ℂ) / y‖ ≤ Rs + 1
    · linarith [abs_nonneg (m : ℝ)]
    push Not at hsmall
    have hfac : ∀ r ∈ R, ‖(x : ℂ) / y‖ - Rs ≤ ‖(x : ℂ) / y - r‖ := by
      intro r hr
      have h1 : ‖r‖ ≤ Rs := Finset.single_le_sum (f := fun r ↦ ‖r‖)
        (fun _ _ ↦ norm_nonneg _) hr
      have h2 := norm_sub_norm_le ((x : ℂ) / y) r
      linarith
    have hP : (‖(x : ℂ) / y‖ - Rs) ^ n ≤ ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by
      rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun _ _ ↦ pow_nonneg (by linarith) _)
        fun r hr ↦ pow_le_pow_left₀ (by linarith) (hfac r hr) _
    have hn1 : n ≠ 0 := by omega
    have hP1 : ‖(x : ℂ) / y‖ - Rs ≤ (‖(x : ℂ) / y‖ - Rs) ^ n := le_self_pow₀ (by linarith) hn1
    have hay : 1 ≤ |(a : ℝ)| * |(y : ℝ)| ^ d := one_le_mul_of_one_le_of_one_le haR
      (one_le_pow₀ hy1)
    have hPnn : 0 ≤ ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r := by positivity
    have : ∏ r ∈ R, ‖(x : ℂ) / y - r‖ ^ rs.count r ≤ |(m : ℝ)| := by
      rw [hidm]; exact le_mul_of_one_le_left hPnn hay
    linarith
  rcases lt_or_eq_of_le hd with hlt | heq
  · -- the form is divisible by `Y`, so `y ∣ m`: no approximation is needed
    have hdiv : ∀ x y : ℤ, y ∣ MvPolynomial.eval ![x, y] (g.homogenize d) := by
      intro x y
      have hsplit : g.homogenize d = MvPolynomial.X 1 * g.homogenize (d - 1) := by
        have := homogenize_mul (1 : ℤ[X]) g (m := 1) (n := d - 1) (by simp) (by omega)
        rw [one_mul, Nat.add_sub_cancel' (by omega)] at this
        rw [this, homogenize_one, pow_one]
      rw [hsplit, map_mul, MvPolynomial.eval_X]
      exact dvd_mul_right _ _
    refine (hImported2 ((Rs + 1 + |(m : ℝ)|) * |(m : ℝ)|) |(m : ℝ)|).subset ?_
    rintro ⟨x, y⟩ hxy
    change MvPolynomial.eval ![x, y] (g.homogenize d) = m at hxy
    have hy : y ≠ 0 := by
      rintro rfl
      rw [hImported7, coeff_eq_zero_of_natDegree_lt hlt, zero_mul] at hxy
      exact hm hxy.symm
    have hym : |(y : ℝ)| ≤ |(m : ℝ)| := by
      have h := Int.le_of_dvd (abs_pos.mpr hm) ((abs_dvd_abs _ _).mpr (hxy ▸ hdiv x y))
      rw [← Int.cast_abs, ← Int.cast_abs]
      exact_mod_cast h
    refine ⟨(hxbound x y hy hxy).trans ?_, hym⟩
    refine mul_le_mul_of_nonneg_left hym ?_
    positivity
  -- the form is not divisible by `Y`, and it has three distinct roots
  have hR3 : 3 ≤ R.card := by simp only [heq, ↓reduceIte, add_zero] at hroots; omega
  have hoff : R.offDiag.Nonempty := by
    obtain ⟨r₁, hr₁, r₂, hr₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < R.card)
    exact ⟨(r₁, r₂), Finset.mem_offDiag.mpr ⟨hr₁, hr₂, h12⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := R.offDiag.exists_min_image (fun p ↦ ‖p.1 - p.2‖) hoff
  set δ : ℝ := ‖p₀.1 - p₀.2‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp₀).2.2)
  have hδle : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → δ ≤ ‖r - r'‖ := fun r hr r' hr' h ↦
    hmin (r, r') (Finset.mem_offDiag.mpr ⟨hr, hr', h⟩)
  set δ' : ℝ := min 1 (δ / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min one_pos (by positivity)
  have hδ'1 : δ' ≤ 1 := min_le_left _ _
  set C : ℝ := |(m : ℝ)| / δ' ^ n with hCdef
  set Y₀ : ℝ := max 1 (2 * max 1 |(m : ℝ)| / δ) with hY₀def
  have hY₀1 : 1 ≤ Y₀ := le_max_left _ _
  -- the exceptional set of each root is finite
  set T : ℂ → Set (ℤ × ℤ) := fun r ↦ {z : ℤ × ℤ | z.2 ≠ 0 ∧ (z.1 : ℂ) / z.2 ≠ r ∧
    ‖(z.1 : ℂ) / z.2 - r‖ ^ rs.count r * |(z.2 : ℝ)| ^ d ≤ C} with hTdef
  have hT : ∀ r ∈ R, (T r).Finite := by
    intro r hr
    have hrs : r ∈ rs := Multiset.mem_toFinset.mp hr
    have halg : IsAlgebraic ℚ r := by
      refine ⟨g.map (Int.castRingHom ℚ),
        (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg, ?_⟩
      have hroot : gc.IsRoot r := (mem_roots hgc0).mp hrs
      rw [aeval_def, eval₂_map]
      rw [IsRoot, hgc, eval_map] at hroot
      convert hroot using 2 <;> rfl
    have hlt : rs.count r < d := by
      obtain ⟨r', hr', hne⟩ : ∃ r' ∈ R, r' ≠ r := by
        by_contra hcon
        push Not at hcon
        have : R.card ≤ 1 := Finset.card_le_one.mpr fun u hu v hv ↦
          (hcon u hu).trans (hcon v hv).symm
        omega
      have h2 : rs.count r + rs.count r' ≤ n := by
        rw [← hsum, ← Finset.sum_pair (f := fun r ↦ rs.count r) hne.symm]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.insert_subset hr (Finset.singleton_subset_iff.mpr hr'))
          fun _ _ _ ↦ Nat.zero_le _
      have := hcount r' hr'
      omega
    refine Complex.finite_setOf_norm_div_sub_pow_mul_pow_le halg (hcount r hr) hlt ?_ C
    intro ξ hξ hirrξ
    rw [← heq]
    refine two_mul_count_roots_lt_natDegree hg hrs ?_ (by omega)
    rintro ⟨c, hc⟩
    apply hirrξ
    refine ⟨c, ?_⟩
    have : ((c : ℝ) : ℂ) = (ξ : ℂ) := by rw [hξ, ← hc]; simp
    exact_mod_cast this
  set X₀ : ℝ := max ((Rs + 1 + |(m : ℝ)|) * Y₀) (max 1 |(m : ℝ)|) with hX₀def
  refine ((hImported2 X₀ Y₀).union
    ((R.finite_toSet).biUnion fun r hr ↦ hT r hr)).subset ?_
  rintro ⟨x, y⟩ hxy
  change MvPolynomial.eval ![x, y] (g.homogenize d) = m at hxy
  by_cases hy : y = 0
  · -- `a x ^ d = m`
    subst hy
    left
    rw [hImported7, ← heq] at hxy
    refine ⟨le_max_of_le_right ?_, by simpa using hY₀1.trans' zero_le_one⟩
    have hxm : |(x : ℝ)| ^ n ≤ |(m : ℝ)| := by
      rw [← hxy]
      push_cast
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (by positivity) haR
    have hn0 : n ≠ 0 := by omega
    exact hImported5 hn0 hxm
  by_cases hsmall : |(y : ℝ)| ≤ Y₀
  · left
    refine ⟨le_max_of_le_left ((hxbound x y hy hxy).trans ?_), hsmall⟩
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  right
  push Not at hsmall
  have hy1 := hImported4 hy
  have hypos : 0 < |(y : ℝ)| := by linarith
  have hidm := hid x y hy
  rw [hxy] at hidm
  set t : ℂ := (x : ℂ) / y with htdef
  set P : ℝ := ∏ r ∈ R, ‖t - r‖ ^ rs.count r with hPdef
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r₀, hr₀, hmin₀⟩ := R.exists_min_image (fun r ↦ ‖t - r‖) hRne
  set ρ : ℝ := ‖t - r₀‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  refine Set.mem_iUnion₂.mpr ⟨r₀, hr₀, hy, ?_, ?_⟩
  · -- `x / y` is not a root, since `G(x, y) = m ≠ 0`
    intro ht
    have hP0 : P = 0 := Finset.prod_eq_zero hr₀ (by
      change ‖t - r₀‖ ^ rs.count r₀ = 0
      rw [show t = r₀ from ht, sub_self, norm_zero, zero_pow (hcount r₀ hr₀).ne'])
    rw [hP0, mul_zero, abs_eq_zero, Int.cast_eq_zero] at hidm
    exact hm hidm
  change ρ ^ rs.count r₀ * |(y : ℝ)| ^ d ≤ C
  -- the nearest root is within `δ / 2`
  have hρn : ρ ^ n ≤ P := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ ↦ pow_nonneg hρ0 _)
      fun r hr ↦ pow_le_pow_left₀ hρ0 (hmin₀ r hr) _
  have hρy : ρ * |(y : ℝ)| ≤ max 1 |(m : ℝ)| := by
    refine hImported5 (μ := n) (by omega) ?_
    rw [mul_pow, heq, hidm]
    rw [← heq]
    calc ρ ^ n * |(y : ℝ)| ^ n ≤ P * |(y : ℝ)| ^ n := by gcongr
      _ = 1 * |(y : ℝ)| ^ n * P := by ring
      _ ≤ |(a : ℝ)| * |(y : ℝ)| ^ n * P := by gcongr
  have hρδ : ρ ≤ δ / 2 := by
    have h1 : 2 * max 1 |(m : ℝ)| / δ < |(y : ℝ)| := (le_max_right _ _).trans_lt hsmall
    rw [div_lt_iff₀ hδ] at h1
    have h2 : ρ * |(y : ℝ)| * 2 ≤ δ * |(y : ℝ)| := by linarith
    have h3 : (ρ * 2) * |(y : ℝ)| ≤ δ * |(y : ℝ)| := by linarith
    have := le_of_mul_le_mul_right h3 hypos
    linarith
  -- every other root is at least `δ / 2` away
  have hfar : ∀ r ∈ R.erase r₀, δ' ≤ ‖t - r‖ := by
    intro r hr
    obtain ⟨hne, hrR⟩ := Finset.mem_erase.mp hr
    have h1 := hδle r hrR r₀ hr₀ hne
    have h2 : ‖r - r₀‖ ≤ ‖t - r‖ + ‖t - r₀‖ := by
      calc ‖r - r₀‖ = ‖(t - r₀) - (t - r)‖ := by ring_nf
        _ ≤ ‖t - r₀‖ + ‖t - r‖ := norm_sub_le _ _
        _ = ‖t - r‖ + ‖t - r₀‖ := add_comm _ _
    have : δ / 2 ≤ ‖t - r‖ := by linarith
    exact (min_le_right _ _).trans this
  have hrest : δ' ^ n ≤ ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r := by
    calc δ' ^ n ≤ δ' ^ (∑ r ∈ R.erase r₀, rs.count r) := by
          refine pow_le_pow_of_le_one hδ'0.le hδ'1 ?_
          rw [← hsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ Nat.zero_le _
      _ = ∏ r ∈ R.erase r₀, δ' ^ rs.count r := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r :=
          Finset.prod_le_prod (fun _ _ ↦ pow_nonneg hδ'0.le _)
            fun r hr ↦ pow_le_pow_left₀ hδ'0.le (hfar r hr) _
  have hPsplit : P = ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r :=
    (Finset.mul_prod_erase R (fun r ↦ ‖t - r‖ ^ rs.count r) hr₀).symm
  rw [hCdef, le_div_iff₀ (pow_pos hδ'0 n), hidm, hPsplit]
  calc ρ ^ rs.count r₀ * |(y : ℝ)| ^ d * δ' ^ n
      ≤ ρ ^ rs.count r₀ * |(y : ℝ)| ^ d * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r := by
        gcongr
    _ = 1 * |(y : ℝ)| ^ d * (ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r) := by
        ring
    _ ≤ |(a : ℝ)| * |(y : ℝ)| ^ d *
        (ρ ^ rs.count r₀ * ∏ r ∈ R.erase r₀, ‖t - r‖ ^ rs.count r) := by
        gcongr
