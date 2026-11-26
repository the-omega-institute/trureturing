/- GID: D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quark mixing invariants, one-loop gauge ratios, and the two-loop QCD coefficient window. -/

import OmegaBuild.Commands
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity

/-- Independent phases on the rows and columns of a mixing matrix. -/
def biRephase {n : ℕ} (α β : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => α i * V i j * star (β j))

def IsUnitPhases {n : ℕ} (α : Fin n → ℂ) : Prop := ∀ i, ‖α i‖ = 1

/-- The quartet uses the two entries on one diagonal of a rectangle and conjugates the other two. -/
def quartet {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (i j k l : Fin n) : ℂ :=
  V i j * V k l * star (V i l) * star (V k j)

theorem quartet_biRephase_invariant {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    {α β : Fin n → ℂ} (hα : IsUnitPhases α) (hβ : IsUnitPhases β) (i j k l : Fin n) :
    quartet (biRephase α β V) i j k l = quartet V i j k l := by
  have phase (z : ℂ) (hz : ‖z‖ = 1) : z * conj z = 1 := by
    rw [Complex.mul_conj', hz]
    norm_num
  calc
    _ = quartet V i j k l *
        ((α i * conj (α i)) * (α k * conj (α k)) *
         (β j * conj (β j)) * (β l * conj (β l))) := by
      simp only [quartet, biRephase, Matrix.of_apply, Complex.star_def, map_mul, conj_conj]
      ring
    _ = _ := by simp [phase _ (hα i), phase _ (hα k), phase _ (hβ j), phase _ (hβ l)]

private theorem quartet_real_of_rephasable {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (h : ∃ α β, IsUnitPhases α ∧ IsUnitPhases β ∧
      ∀ i j, (biRephase α β V i j).im = 0) (i j k l : Fin n) :
    (quartet V i j k l).im = 0 := by
  obtain ⟨α, β, hα, hβ, hreal⟩ := h
  rw [← quartet_biRephase_invariant V hα hβ i j k l]
  simp [quartet, Complex.mul_im, hreal]

private theorem row_inner {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ unitaryGroup (Fin n) ℂ) (i k : Fin n) :
    ∑ j, V i j * conj (V k j) = if i = k then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i k)
    (Matrix.mem_unitaryGroup_iff.mp hV)
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply, Complex.star_def] using h

private theorem col_inner {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ unitaryGroup (Fin n) ℂ) (j l : Fin n) :
    ∑ i, V i j * conj (V i l) = if j = l then 1 else 0 := by
  simpa [Matrix.transpose_apply] using
    row_inner (Matrix.transpose_mem_unitaryGroup_iff.mpr hV) j l

private def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem norm_unitPhase (z : ℂ) : ‖unitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · simp [unitPhase, hz, norm_ne_zero_iff.mpr hz]

private theorem star_unitPhase_mul_self (z : ℂ) :
    conj (unitPhase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  simp only [unitPhase, ite_eq_right hz, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
    Complex.conj_mul']
  field_simp

private theorem real_rephase_of_pivot {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (r : Fin n)
    (hcover : ∀ i j k, j ≠ k → V i j ≠ 0 → V i k ≠ 0 → V r j ≠ 0 ∧ V r k ≠ 0)
    (hquartet : ∀ i j k l, (quartet V i j k l).im = 0) :
    ∃ α β, IsUnitPhases α ∧ IsUnitPhases β ∧
      ∀ i j, (biRephase α β V i j).im = 0 := by
  classical
  let β (j : Fin n) := unitPhase (V r j)
  let W := biRephase (fun _ => 1) β V
  have hβ : IsUnitPhases β := fun j => norm_unitPhase (V r j)
  have hW (i j : Fin n) : W i j = V i j * conj (β j) := by
    simp [W, biRephase]
  have hpivot (j : Fin n) : W r j = (‖V r j‖ : ℂ) := by
    rw [hW, mul_comm]
    exact star_unitPhase_mul_self (V r j)
  have hpair (i j k : Fin n) : (W i j * conj (W i k)).im = 0 := by
    by_cases hjk : j = k
    · subst k
      simp [Complex.mul_conj', ← Complex.ofReal_pow]
    by_cases hj : V i j = 0
    · simp [hW, hj]
    by_cases hk : V i k = 0
    · simp [hW, hk]
    obtain ⟨hrj, hrk⟩ := hcover i j k hjk hj hk
    have h := hquartet i j r k
    rw [← quartet_biRephase_invariant V (α := fun _ => 1) (by simp [IsUnitPhases]) hβ] at h
    change (quartet W i j r k).im = 0 at h
    have hfact : quartet W i j r k = (W i j * conj (W i k)) *
        ((‖V r j‖ * ‖V r k‖ : ℝ) : ℂ) := by
      simp only [quartet, hpivot, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rwa [hfact, Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add, Complex.ofReal_re,
      mul_eq_zero, or_iff_left (mul_ne_zero (norm_ne_zero_iff.mpr hrj)
        (norm_ne_zero_iff.mpr hrk))] at h
  let α (i : Fin n) := if h : ∃ j, W i j ≠ 0 then conj (unitPhase (W i h.choose)) else 1
  refine ⟨α, β, ?_, hβ, ?_⟩
  · intro i
    by_cases hi : ∃ j, W i j ≠ 0 <;> simp [α, hi, norm_unitPhase]
  · intro i j
    have hentry : biRephase α β V i j = α i * W i j := by
      simp [biRephase, hW, mul_assoc]
    rw [hentry]
    by_cases hi : ∃ k, W i k ≠ 0
    · have hn := hi.choose_spec
      simp only [α, dite_eq_left hi, unitPhase, ite_eq_right hn, map_div₀, Complex.conj_ofReal,
        div_mul_eq_mul_div]
      rw [mul_comm (conj (W i hi.choose)), Complex.div_im]
      simp [hpair i j hi.choose]
    · have hz : W i j = 0 := by by_contra h; exact hi ⟨j, h⟩
      simp [hz]

private theorem quartet_im_diag_row {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i j l : Fin n) : (quartet V i j i l).im = 0 := by
  simp [quartet, Complex.mul_im, Complex.mul_re]
  ring

private theorem quartet_im_diag_col {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i j k : Fin n) : (quartet V i j k j).im = 0 := by
  simp [quartet, Complex.mul_im, Complex.mul_re]
  ring

private theorem quartet_im_swap_row {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i j k l : Fin n) : (quartet V k j i l).im = -(quartet V i j k l).im := by
  simp [quartet, Complex.mul_im, Complex.mul_re]
  ring

private theorem quartet_im_swap_col {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (i j k l : Fin n) : (quartet V i l k j).im = -(quartet V i j k l).im := by
  simp [quartet, Complex.mul_im, Complex.mul_re]
  ring

private theorem quartet_im_sum_col {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ unitaryGroup (Fin n) ℂ) (i j k : Fin n) :
    ∑ l, (quartet V i j k l).im = 0 := by
  by_cases hik : i = k
  · subst k
    simp [quartet_im_diag_row]
  have h (l : Fin n) : quartet V i j k l =
      (V i j * conj (V k j)) * (V k l * conj (V i l)) := by
    simp only [quartet, Complex.star_def]
    ring
  simp only [← Complex.im_sum, h, ← Finset.mul_sum, row_inner hV k i, ite_eq_right (Ne.symm hik),
    mul_zero, Complex.zero_im]

private theorem quartet_im_sum_row {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ unitaryGroup (Fin n) ℂ) (i j l : Fin n) :
    ∑ k, (quartet V i j k l).im = 0 := by
  by_cases hjl : j = l
  · subst l
    simp [quartet_im_diag_col]
  have h (k : Fin n) : quartet V i j k l =
      (V i j * conj (V i l)) * (V k l * conj (V k j)) := by
    simp only [quartet, Complex.star_def]
    ring
  simp only [← Complex.im_sum, h, ← Finset.mul_sum, col_inner hV l j, ite_eq_right (Ne.symm hjl),
    mul_zero, Complex.zero_im]

/-- In dimension two, each row-orthogonality relation leaves one imaginary quartet. -/
theorem u2_all_quartets_real {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ unitaryGroup (Fin 2) ℂ) (i j k l : Fin 2) :
    (quartet V i j k l).im = 0 := by
  have h := quartet_im_sum_col hV i j k
  rw [Fin.sum_univ_two] at h
  have hdiag := quartet_im_diag_col V i j k
  fin_cases j <;> fin_cases l <;> simp_all

/-- Every two-dimensional unitary mixing matrix admits a real representative. -/
theorem u2_real_rephasable {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V ∈ unitaryGroup (Fin 2) ℂ) :
    ∃ α β, IsUnitPhases α ∧ IsUnitPhases β ∧
      ∀ i j, (biRephase α β V i j).im = 0 := by
  by_cases h : ∃ r, ∀ j, V r j ≠ 0
  · obtain ⟨r, hr⟩ := h
    exact real_rephase_of_pivot V r (fun _ j k _ _ _ => ⟨hr j, hr k⟩) (u2_all_quartets_real hV)
  push Not at h
  apply real_rephase_of_pivot V 0 _ (u2_all_quartets_real hV)
  intro i j k hjk hj hk
  obtain ⟨l, hl⟩ := h i
  fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

/-- A nonreal quartet in a unitary mixing matrix requires at least three generations. -/
theorem cp_violation_requires_three_generations {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {i j k l : Fin n} (h : (quartet V i j k l).im ≠ 0) :
    3 ≤ n := by
  by_contra! hn
  have hsmall : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hsmall with h0 | h1 | h2
  · subst n
    exact Fin.elim0 i
  · subst n
    have he : k = i := Subsingleton.elim _ _
    subst k
    exact h (quartet_im_diag_row V i j l)
  · subst n
    exact h (u2_all_quartets_real hV i j k l)

/-- The orientation fixes the positive quartet to rows 0, 1 and columns 1, 2. -/
def jarlskog (V : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := (quartet V 0 1 1 2).im

/-- The alternating symbol with epsilon(0, 1, 2) equal to +1. -/
def eps3 (i k m : Fin 3) : ℝ :=
  if i = k ∨ k = m ∨ m = i then 0 else if i + 1 = k then 1 else -1

private theorem alternating_three (f : Fin 3 → Fin 3 → ℝ)
    (hdiag : ∀ i, f i i = 0) (hswap : ∀ i k, f k i = -f i k)
    (hsum : ∀ i, ∑ k, f i k = 0) (i k : Fin 3) :
    f i k = f 0 1 * ∑ m, eps3 i k m := by
  have h₀ := hsum 0
  have h₁ := hsum 1
  rw [Fin.sum_univ_three, hdiag] at h₀ h₁
  have h01 := hswap 0 1
  have h02 := hswap 0 2
  have h12 := hswap 1 2
  fin_cases i <;> fin_cases k <;>
    norm_num [Fin.sum_univ_three, eps3, hdiag] <;> linarith

theorem jarlskog_universal_all_quartets {V : Matrix (Fin 3) (Fin 3) ℂ}
    (hV : V ∈ unitaryGroup (Fin 3) ℂ) (i j k l : Fin 3) :
    (quartet V i j k l).im =
      jarlskog V * (∑ m : Fin 3, ∑ n : Fin 3, eps3 i k m * eps3 j l n) := by
  have hrow := alternating_three (fun i k => (quartet V i j k l).im)
    (fun i => quartet_im_diag_row V i j l) (fun i k => quartet_im_swap_row V i j k l)
    (fun i => quartet_im_sum_row hV i j l) i k
  have hcol := alternating_three (fun j l => (quartet V 0 j 1 l).im)
    (fun j => quartet_im_diag_col V 0 j 1) (fun j l => quartet_im_swap_col V 0 j 1 l)
    (quartet_im_sum_col hV 0 · 1)
  have h12 : (quartet V 0 1 1 2).im = (quartet V 0 0 1 1).im := by
    simpa [eps3, Fin.sum_univ_three] using hcol 1 2
  rw [hrow, hcol j l, ← h12]
  simp only [jarlskog, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem u3_support_pivot {V : Matrix (Fin 3) (Fin 3) ℂ}
    (hV : V ∈ unitaryGroup (Fin 3) ℂ) :
    ∃ r, ∀ i j k, j ≠ k → V i j ≠ 0 → V i k ≠ 0 → V r j ≠ 0 ∧ V r k ≠ 0 := by
  by_cases full : ∃ r, ∀ j, V r j ≠ 0
  · obtain ⟨r, hr⟩ := full
    exact ⟨r, fun _ j k _ _ _ => ⟨hr j, hr k⟩⟩
  push Not at full
  have miss (i : Fin 3) : V i 0 = 0 ∨ V i 1 = 0 ∨ V i 2 = 0 := by
    obtain ⟨j, hj⟩ := full i
    fin_cases j <;> tauto
  by_cases pair : ∃ r j k, j ≠ k ∧ V r j ≠ 0 ∧ V r k ≠ 0
  · obtain ⟨r, a, b, hab, hra, hrb⟩ := pair
    refine ⟨r, fun i j k hjk hij hik => ?_⟩
    by_cases hir : i = r
    · subst i
      exact ⟨hij, hik⟩
    have orth := row_inner hV i r
    rw [ite_eq_right hir, Fin.sum_univ_three] at orth
    have hm := miss r
    have hn := miss i
    have hzero (x y z : ℂ) (h : x + y + z = 0) :
        (x = 0 → y = 0 → z = 0) ∧ (x = 0 → z = 0 → y = 0) ∧
          (y = 0 → z = 0 → x = 0) := by
      refine ⟨fun hx hy => ?_, fun hx hz => ?_, fun hy hz => ?_⟩ <;> simp_all
    have hz := hzero _ _ _ orth
    simp only [mul_eq_zero, map_eq_zero] at hz
    clear full miss orth hzero
    fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases k <;>
      simp_all
  push Not at pair
  exact ⟨0, fun i j k hjk hij hik => (hik (pair i j k hjk hij)).elim⟩

theorem u3_jarlskog_zero_iff_real_rephasable {V : Matrix (Fin 3) (Fin 3) ℂ}
    (hV : V ∈ unitaryGroup (Fin 3) ℂ) :
    jarlskog V = 0 ↔ ∃ α β, IsUnitPhases α ∧ IsUnitPhases β ∧
      ∀ i j, (biRephase α β V i j).im = 0 := by
  constructor
  · intro hJ
    obtain ⟨r, hr⟩ := u3_support_pivot hV
    exact real_rephase_of_pivot V r hr (fun i j k l => by
      simp [jarlskog_universal_all_quartets hV, hJ])
  · intro h
    exact quartet_real_of_rephasable h 0 1 1 2

private theorem amgm_cube {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  have hcube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
    rw [← Real.rpow_mul_natCast hx]
    norm_num
  have hpow := pow_le_pow_left₀ (by positivity) h 3
  simp only [mul_pow, hcube a ha, hcube b hb, hcube c hc] at hpow
  convert hpow using 1
  congr 1
  ring

/-- Twice the area of the triangle of row products is the absolute quartet invariant. -/
private theorem triangle_im_bound (a b c : ℂ) (h : a + b + c = 0)
    (hp : ‖a‖ + ‖b‖ + ‖c‖ ≤ 1) : |(b * conj c).im| ≤ 1 / (6 * Real.sqrt 3) := by
  let x := ‖a‖
  let y := ‖b‖
  let z := ‖c‖
  let p := x + y + z
  have hc : c = -(a + b) := by linear_combination h
  have ha : a = -(b + c) := by linear_combination h
  have hb : b = -(c + a) := by linear_combination h
  have hx : x ≤ y + z := by simpa only [x, y, z, ha, norm_neg] using norm_add_le b c
  have hy : y ≤ z + x := by simpa only [x, y, z, hb, norm_neg] using norm_add_le c a
  have hz : z ≤ x + y := by simpa only [x, y, z, hc, norm_neg] using norm_add_le a b
  have heron : 4 * (b * conj c).im ^ 2 =
      p * ((x + y - z) * (y + z - x) * (z + x - y)) := by
    calc
      _ = 2 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)
            - x ^ 4 - y ^ 4 - z ^ 4 := by
        simp only [x, y, z, show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.sq_norm,
          hc, Complex.normSq_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im]
        ring
      _ = _ := by dsimp [p]; ring
  have hmean := amgm_cube
    (sub_nonneg.mpr hz) (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  have hsum : (x + y - z) + (y + z - x) + (z + x - y) = p := by dsimp [p]; ring
  rw [hsum] at hmean
  have hp0 : 0 ≤ p := by dsimp [p, x, y, z]; positivity
  have hp3 : (p / 3) ^ 3 ≤ (1 / 3 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith : p / 3 ≤ 1 / 3) 3
  have hprod := (mul_le_mul_of_nonneg_left hmean hp0).trans
    (mul_le_mul hp hp3 (by positivity) (by norm_num))
  rw [← heron] at hprod
  norm_num at hprod
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, div_pow, mul_pow, hsq]
  norm_num
  linarith

theorem jarlskog_abs_le_sharp {V : Matrix (Fin 3) (Fin 3) ℂ}
    (hV : V ∈ unitaryGroup (Fin 3) ℂ) :
    |jarlskog V| ≤ 1 / (6 * Real.sqrt 3) := by
  let a (j : Fin 3) := V 0 j * conj (V 1 j)
  have hs : a 0 + a 1 + a 2 = 0 := by simpa [a, Fin.sum_univ_three] using row_inner hV 0 1
  have hn (i : Fin 3) : ∑ j, ‖V i j‖ ^ 2 = 1 := by
    have h := row_inner hV i i
    rw [ite_eq_left (rfl : i = i)] at h
    simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
      ← Complex.ofReal_one, Complex.ofReal_inj] using h
  have hab (j : Fin 3) : ‖a j‖ ≤ (‖V 0 j‖ ^ 2 + ‖V 1 j‖ ^ 2) / 2 := by
    rw [show ‖a j‖ = ‖V 0 j‖ * ‖V 1 j‖ by simp [a]]
    nlinarith [sq_nonneg (‖V 0 j‖ - ‖V 1 j‖)]
  have hp : ‖a 0‖ + ‖a 1‖ + ‖a 2‖ ≤ 1 := by
    have h0 := hn 0
    have h1 := hn 1
    rw [Fin.sum_univ_three] at h0 h1
    linarith [hab 0, hab 1, hab 2]
  have hq : a 1 * conj (a 2) = quartet V 0 1 1 2 := by
    simp only [a, quartet, Complex.star_def, map_mul, conj_conj]
    ring
  simpa [hq, jarlskog] using triangle_im_bound _ _ _ hs hp

private def omega3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private def fourierCore : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, omega3, conj omega3; 1, conj omega3, omega3]

/-- The normalized three-point Fourier matrix with the positive imaginary cube root. -/
def fourier3 : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 / Real.sqrt 3 : ℝ) : ℂ) • Matrix.of (fun i j : Fin 3 => omega3 ^ (i.val * j.val))

private theorem fourierCore_entries (i j : Fin 3) :
    fourierCore i j = omega3 ^ (i.val * j.val) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hw2 : omega3 ^ (2 : ℕ) = conj omega3 := by
    apply Complex.ext <;> norm_num [omega3, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hw3 : omega3 ^ (3 : ℕ) = 1 := by
    rw [pow_succ, hw2]
    apply Complex.ext <;> norm_num [omega3, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hw4 : omega3 ^ (4 : ℕ) = omega3 := by rw [pow_succ, hw3, one_mul]
  fin_cases i <;> fin_cases j <;> norm_num [fourierCore, hw2, hw4]

theorem fourier3_attains_max_jarlskog :
    fourier3 ∈ unitaryGroup (Fin 3) ℂ ∧ |jarlskog fourier3| = 1 / (6 * Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hF : fourier3 = ((1 / Real.sqrt 3 : ℝ) : ℂ) • fourierCore := by
    ext i j
    simp [fourier3, fourierCore_entries]
  have hcore : fourierCore * star fourierCore = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [fourierCore, omega3, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three,
        Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;>
      nlinarith
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    rw [hF, star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, hcore, smul_smul, smul_smul]
    have hs' : (↑(1 / Real.sqrt 3) : ℂ) * ↑(1 / Real.sqrt 3) * 3 = 1 := by
      push_cast
      field_simp
      exact_mod_cast hsq.symm
    rw [hs', one_smul]
  · have hpos : jarlskog fourier3 = 1 / (6 * Real.sqrt 3) := by
      rw [hF]
      norm_num [jarlskog, quartet, fourierCore, omega3, Matrix.smul_apply, smul_eq_mul,
        Complex.mul_im, Complex.mul_re]
      field_simp
      ring_nf
      have h6 : (Real.sqrt 3) ^ (6 : ℕ) = 27 := by
        rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, hsq]
        norm_num
      norm_num [h6]
    rw [hpos, abs_of_nonneg (by positivity)]

/-- Product of the three increasing-index differences. -/
def vandermonde3 (d : Fin 3 → ℝ) : ℝ :=
  (d 1 - d 0) * (d 2 - d 0) * (d 2 - d 1)

private abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
private def massDiagonal (d : Fin 3 → ℝ) : M3 := diagonal fun i => (d i : ℂ)

private def columnProduct (V : M3) (j i k : Fin 3) : ℂ := V i j * conj (V k j)

private theorem mixed_cycle (V : M3) (hV : V ∈ unitaryGroup (Fin 3) ℂ) (j l : Fin 3) :
    (columnProduct V l 0 1 * columnProduct V j 1 2 * columnProduct V j 2 0 +
     columnProduct V j 0 1 * columnProduct V l 1 2 * columnProduct V j 2 0 +
     columnProduct V j 0 1 * columnProduct V j 1 2 * columnProduct V l 2 0).im =
      jarlskog V * ∑ m, eps3 l j m := by
  let e := ∑ m, eps3 l j m
  have h01 : (quartet V 0 l 1 j).im = jarlskog V * e := by
    simpa [e, Fin.sum_univ_three, eps3] using jarlskog_universal_all_quartets hV 0 l 1 j
  have h12 : (quartet V 1 l 2 j).im = jarlskog V * e := by
    simpa [e, Fin.sum_univ_three, eps3] using jarlskog_universal_all_quartets hV 1 l 2 j
  have h20 : (quartet V 2 l 0 j).im = jarlskog V * e := by
    simpa [e, Fin.sum_univ_three, eps3] using jarlskog_universal_all_quartets hV 2 l 0 j
  have hterm (i k m : Fin 3) :
      columnProduct V l i k * columnProduct V j k m * columnProduct V j m i =
        (‖V m j‖ : ℂ) ^ 2 * quartet V i l k j := by
    rw [← Complex.mul_conj']
    simp only [columnProduct, quartet, Complex.star_def]
    ring
  have hcol : ‖V 0 j‖ ^ 2 + ‖V 1 j‖ ^ 2 + ‖V 2 j‖ ^ 2 = 1 := by
    have h := col_inner hV j j
    rw [ite_eq_left (rfl : j = j)] at h
    simpa only [Fin.sum_univ_three, Complex.mul_conj', ← Complex.ofReal_pow,
      ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.ofReal_inj] using h
  have hrot1 : columnProduct V j 0 1 * columnProduct V l 1 2 * columnProduct V j 2 0 =
      columnProduct V l 1 2 * columnProduct V j 2 0 * columnProduct V j 0 1 := by ring
  have hrot2 : columnProduct V j 0 1 * columnProduct V j 1 2 * columnProduct V l 2 0 =
      columnProduct V l 2 0 * columnProduct V j 0 1 * columnProduct V j 1 2 := by ring
  rw [hrot1, hrot2, hterm 0 1 2, hterm 1 2 0, hterm 2 0 1]
  simp only [Complex.add_im, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, h01, h12, h20]
  change _ = jarlskog V * e
  linear_combination (jarlskog V * e) * hcol

private theorem pure_cycle (V : M3) (j : Fin 3) :
    (columnProduct V j 0 1 * columnProduct V j 1 2 * columnProduct V j 2 0).im = 0 := by
  have he : columnProduct V j 0 1 * columnProduct V j 1 2 * columnProduct V j 2 0 =
      (V 0 j * conj (V 0 j)) * (V 1 j * conj (V 1 j)) * (V 2 j * conj (V 2 j)) := by
    unfold columnProduct
    ring
  rw [he]
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]

private theorem down_cycle_im (V : M3) (hV : V ∈ unitaryGroup (Fin 3) ℂ) (d : Fin 3 → ℝ) :
    let B := V * massDiagonal d * star V
    (B 0 1 * B 1 2 * B 2 0).im = jarlskog V * vandermonde3 d := by
  intro B
  let x := d 1 - d 0
  let y := d 2 - d 0
  have hB (i k : Fin 3) (hik : i ≠ k) :
      B i k = (x : ℂ) * columnProduct V 1 i k + (y : ℂ) * columnProduct V 2 i k := by
    have orth := row_inner hV i k
    rw [ite_eq_right hik, Fin.sum_univ_three] at orth
    simp only [B, massDiagonal]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply,
      Complex.star_def, Fin.sum_univ_three, x, y, columnProduct, Complex.ofReal_sub]
    linear_combination (d 0 : ℂ) * orth
  rw [hB 0 1 (by decide), hB 1 2 (by decide), hB 2 0 (by decide)]
  have expand (a b c e f g s t : ℂ) :
      (s * a + t * e) * (s * b + t * f) * (s * c + t * g) =
        s ^ 3 * (a * b * c) + t ^ 3 * (e * f * g) +
        (s ^ 2 * t) * (e * b * c + a * f * c + a * b * g) +
        (t ^ 2 * s) * (a * f * g + e * b * g + e * f * c) := by ring
  rw [expand]
  have hx := mixed_cycle V hV 1 2
  have hy := mixed_cycle V hV 2 1
  have hneg : (∑ m : Fin 3, eps3 2 1 m) = -1 := by norm_num [Fin.sum_univ_three, eps3]
  have hpos : (∑ m : Fin 3, eps3 1 2 m) = 1 := by norm_num [Fin.sum_univ_three, eps3]
  rw [hneg, mul_neg_one] at hx
  rw [hpos, mul_one] at hy
  have scale (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by simp [Complex.mul_im]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.add_im, scale,
    pure_cycle, hx, hy, mul_zero, zero_add]
  dsimp [vandermonde3, x, y]
  ring

private theorem det_diagonal_commutator (d : Fin 3 → ℝ) (B : M3)
    (hB : star B = B) :
    Matrix.det (-I • (massDiagonal d * B - B * massDiagonal d)) =
      -2 * ((B 0 1 * B 1 2 * B 2 0).im : ℂ) * (vandermonde3 d : ℂ) := by
  let P := B 0 1 * B 1 2 * B 2 0
  let C := massDiagonal d * B - B * massDiagonal d
  have hC (i k : Fin 3) : C i k = ((d i - d k : ℝ) : ℂ) * B i k := by
    simp [C, massDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, sub_mul, mul_comm (B i k)]
  have hrev (i k : Fin 3) : B k i = conj (B i k) := by
    simpa only [Matrix.star_apply, Complex.star_def] using
      (congrArg (fun M : M3 => M k i) hB).symm
  have hd : Matrix.det C = (vandermonde3 d : ℂ) * (P - conj P) := by
    rw [Matrix.det_fin_three]
    simp only [hC, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero,
      zero_add, hrev 0 1, hrev 1 2, hrev 2 0]
    simp only [P, vandermonde3, map_mul, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  have him : P - conj P = 2 * (P.im : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  have hi : (-I) ^ (3 : ℕ) = I := by rw [pow_succ, neg_sq, Complex.I_sq]; ring
  change Matrix.det (-I • C) = -2 * (P.im : ℂ) * (vandermonde3 d : ℂ)
  rw [Matrix.det_smul, Fintype.card_fin, hi, hd, him]
  calc
    _ = 2 * (P.im : ℂ) * (vandermonde3 d : ℂ) * (I * I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem jarlskog_commutator_det {Uu Ud : M3}
    (hu : Uu ∈ unitaryGroup (Fin 3) ℂ) (hd : Ud ∈ unitaryGroup (Fin 3) ℂ)
    (du dd : Fin 3 → ℝ) :
    let Hu := Uu * diagonal (fun i => (du i : ℂ)) * Uuᴴ
    let Hd := Ud * diagonal (fun i => (dd i : ℂ)) * Udᴴ
    let V := Uuᴴ * Ud
    Matrix.det (-I • (Hu * Hd - Hd * Hu)) =
      -2 * (jarlskog V : ℂ) * (vandermonde3 du : ℂ) * (vandermonde3 dd : ℂ) := by
  intro Hu Hd V
  let A := massDiagonal du
  let B := V * massDiagonal dd * star V
  have hu₁ := Matrix.mem_unitaryGroup_iff.mp hu
  have hu₂ := Matrix.mem_unitaryGroup_iff'.mp hu
  have hv : V ∈ unitaryGroup (Fin 3) ℂ := by
    apply mul_mem _ hd
    rw [← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff, star_star, hu₂]
  have hB : star B = B := by
    have hdiag : star (massDiagonal dd) = massDiagonal dd := by
      ext i j
      by_cases h : i = j <;> simp [massDiagonal, Matrix.star_apply, h, eq_comm]
    simp only [B, star_mul, star_star, hdiag, Matrix.mul_assoc]
  have cancel₁ (X : M3) : Uu * (star Uu * X) = X := by rw [← Matrix.mul_assoc, hu₁, one_mul]
  have cancel₂ (X : M3) : star Uu * (Uu * X) = X := by rw [← Matrix.mul_assoc, hu₂, one_mul]
  have hHd : Hd = Uu * B * star Uu := by
    change Ud * massDiagonal dd * star Ud = Uu * B * star Uu
    simp only [B, V, ← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc,
      cancel₁, hu₁, mul_one]
  have hcomm : Hu * Hd - Hd * Hu = Uu * (A * B - B * A) * star Uu := by
    change (Uu * A * star Uu) * Hd - Hd * (Uu * A * star Uu) = _
    simp only [hHd, mul_sub, sub_mul, Matrix.mul_assoc, cancel₂]
  have hdet : Uu.det * (star Uu).det = 1 := by rw [← Matrix.det_mul, hu₁, Matrix.det_one]
  have hsimilar (X : M3) : (Uu * X * star Uu).det = X.det := by
    simp only [Matrix.det_mul]
    rw [mul_right_comm, hdet, one_mul]
  rw [hcomm, Matrix.det_smul, hsimilar, ← Matrix.det_smul,
    det_diagonal_commutator du B hB, down_cycle_im V hv dd, Complex.ofReal_mul]
  ring

def b1_sm (Ng NH : ℚ) : ℚ := (4 / 3) * Ng + (1 / 10) * NH
def b2_sm (Ng NH : ℚ) : ℚ := -22 / 3 + (4 / 3) * Ng + (1 / 6) * NH
def b3_sm (Ng : ℚ) : ℚ := -11 + (4 / 3) * Ng
def b1_mssm (Ng : ℚ) : ℚ := 2 * Ng + 3 / 5
def b2_mssm (Ng : ℚ) : ℚ := -5 + 2 * Ng
def b3_mssm (Ng : ℚ) : ℚ := -9 + 2 * Ng

def unificationRatio (b1 b2 b3 : ℚ) : ℚ := (b2 - b3) / (b1 - b2)

theorem sm_unification_ratio_generation_independent (Ng NH : ℚ) (hNH : NH ≠ 110) :
    unificationRatio (b1_sm Ng NH) (b2_sm Ng NH) (b3_sm Ng) =
      (110 + 5 * NH) / (220 - 2 * NH) := by
  have h : 220 - 2 * NH ≠ 0 := by intro he; apply hNH; linarith
  unfold unificationRatio b1_sm b2_sm b3_sm
  rw [show -22 / 3 + 4 / 3 * Ng + 1 / 6 * NH - (-11 + 4 / 3 * Ng) =
    (110 + 5 * NH) / 30 by ring]
  rw [show 4 / 3 * Ng + 1 / 10 * NH - (-22 / 3 + 4 / 3 * Ng + 1 / 6 * NH) =
    (220 - 2 * NH) / 30 by ring]
  field_simp

theorem sm_mssm_unification_ratios (Ng : ℚ) :
    unificationRatio (b1_sm Ng 1) (b2_sm Ng 1) (b3_sm Ng) = 115 / 218 ∧
    unificationRatio (b1_mssm Ng) (b2_mssm Ng) (b3_mssm Ng) = 5 / 7 ∧
    (115 / 218 : ℚ) ≠ 5 / 7 := by
  rw [sm_unification_ratio_generation_independent Ng 1 (by norm_num)]
  have h₂ : b2_mssm Ng - b3_mssm Ng = 4 := by unfold b2_mssm b3_mssm; ring
  have h₁ : b1_mssm Ng - b2_mssm Ng = 28 / 5 := by unfold b1_mssm b2_mssm; ring
  norm_num [unificationRatio, h₁, h₂]

def b0_qcd (Nc Ng : ℚ) : ℚ := (11 / 3) * Nc - (4 / 3) * Ng

def b1_qcd (Nc Ng : ℚ) : ℚ :=
  (34 / 3) * Nc ^ 2 - ((10 / 3) * Nc + (Nc ^ 2 - 1) / Nc) * (2 * Ng)

/-- Positivity of both coefficients with the three-generation lower bound gives the window. -/
theorem qcd_confinement_and_cp_generation_window (Ng : ℕ) :
    (0 < b0_qcd 3 Ng ↔ Ng ≤ 8) ∧ (0 < b1_qcd 3 Ng ↔ Ng ≤ 4) ∧
    (3 ≤ Ng ∧ 0 < b0_qcd 3 Ng ∧ 0 < b1_qcd 3 Ng ↔ Ng = 3 ∨ Ng = 4) := by
  have h₀ : 0 < b0_qcd 3 Ng ↔ Ng ≤ 8 := by
    unfold b0_qcd
    constructor
    · intro h
      by_contra! hN
      have hcast : (9 : ℚ) ≤ Ng := by exact_mod_cast hN
      linarith
    · intro h
      have hcast : (Ng : ℚ) ≤ 8 := by exact_mod_cast h
      linarith
  have h₁ : 0 < b1_qcd 3 Ng ↔ Ng ≤ 4 := by
    unfold b1_qcd
    constructor
    · intro h
      by_contra! hN
      have hcast : (5 : ℚ) ≤ Ng := by exact_mod_cast hN
      linarith
    · intro h
      have hcast : (Ng : ℚ) ≤ 4 := by exact_mod_cast h
      linarith
  exact ⟨h₀, h₁, by rw [h₀, h₁]; omega⟩

end D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity
