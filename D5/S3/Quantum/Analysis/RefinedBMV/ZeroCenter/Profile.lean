/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Profile
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A convex logarithmic profile for the zero-centered upper refined BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeDerivatives
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.MatrixLift
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Moments
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FunProp

/-! The normalized zero-centered kernel and its finite interval representation. -/

open Filter Matrix Set
open scoped BigOperators ComplexOrder Topology

noncomputable section

namespace RefinedBMV.FourSpectrumLift

open DimThree (defect)
open DividedDifference (defect_eq_homogeneous homogeneousTwo homogeneousThree)
open ExtremeWalk (upperKernel)
open Extreme (normalized)
open UniformThreeSpectrum (defect_cycle_all)

universe u

private theorem convex_rectangle {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f)
    {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    f (x + a) + f (x + b) ≤ f x + f (x + a + b) := by
  by_cases h : a + b = 0
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    simp [ha', hb']
  let s := a / (a + b)
  let t := b / (a + b)
  have hs : 0 ≤ s := div_nonneg ha (add_nonneg ha hb)
  have ht : 0 ≤ t := div_nonneg hb (add_nonneg ha hb)
  have hst : s + t = 1 := by dsimp [s, t]; field_simp [h]
  have hx' : x ∈ Ici (0 : ℝ) := hx
  have hy : x + a + b ∈ Ici (0 : ℝ) := by exact add_nonneg (add_nonneg hx ha) hb
  have h₁ := hf.2 hx' hy ht hs (by linarith)
  have h₂ := hf.2 hx' hy hs ht hst
  have e₁ : t * x + s * (x + a + b) = x + a := by
    dsimp [s, t]
    field_simp [h]
    ring
  have e₂ : s * x + t * (x + a + b) = x + b := by
    dsimp [s, t]
    field_simp [h]
    ring
  simp only [smul_eq_mul, e₁] at h₁
  simp only [smul_eq_mul, e₂] at h₂
  have e : t * f x + s * f (x + a + b) + (s * f x + t * f (x + a + b)) =
      f x + f (x + a + b) := by
    linear_combination (f x + f (x + a + b)) * hst
  exact e ▸ add_le_add h₁ h₂

private theorem antitoneOn_of_convex_limit {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ici 0) f) (hlim : Tendsto f atTop (𝓝 0)) : AntitoneOn f (Ici 0) := by
  intro x hx y _ hxy
  have hshift : Tendsto (fun z : ℝ ↦ z + (y - x)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hdiff : Tendsto (fun z : ℝ ↦ f (z + (y - x)) - f z) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_zero] using (hlim.comp hshift).sub hlim
  apply sub_nonpos.mp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hdiff
  filter_upwards [eventually_ge_atTop x] with z hz
  have hr := convex_rectangle hf hx (sub_nonneg.mpr hxy) (sub_nonneg.mpr hz)
  rw [show x + (y - x) = y by ring, show x + (z - x) = z by ring,
      show y + (z - x) = z + (y - x) by ring] at hr
  linarith

private theorem profile_gram_posSemidef {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ici 0) f) (hlim : Tendsto f atTop (𝓝 0))
    {ι : Type u} [Finite ι] (x : ι → ℝ) :
    (Matrix.of fun i j ↦ f (max (x i) (x j) - min (x i) (x j))).PosSemidef := by
  letI := Fintype.ofFinite ι
  have hanti := antitoneOn_of_convex_limit hf hlim
  have hn (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [eventually_ge_atTop t] with z hz
    exact hanti ht (ht.trans hz) hz
  let n := Fintype.card ι
  let e := (Fintype.equivFin ι).symm
  let order : Fin n ≃ ι := (Tuple.sort (x ∘ e)).trans e
  let y := x ∘ order
  have hmono : Monotone y := Tuple.monotone_sort (x ∘ e)
  apply (Matrix.posSemidef_submatrix_equiv order).mp
  change (Matrix.of fun i j ↦ f (max (y i) (y j) - min (y i) (y j))).PosSemidef
  let z (i : ℕ) := if h : i < n then y ⟨i, h⟩ else 0
  let A (i j : ℕ) := if i = 0 ∨ n < j then 0 else f (z (j - 1) - z (i - 1))
  have hle (i j : ℕ) (hij : i ≤ j) (hj : j < n) : z i ≤ z j := by
    have hi := hij.trans_lt hj
    simpa [z, hi, hj] using hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hinside (i j : ℕ) (hj : j < n) : A (i + 1) (j + 1) = f (z j - z i) := by
    simp [A, show ¬ n < j + 1 by omega]
  have hrow (j : ℕ) : A 0 j = 0 := by simp [A]
  have hcol (i : ℕ) : A i (n + 1) = 0 := by simp [A]
  have hrect (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
      0 ≤ (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2)) := by
    rw [hinside i j hj]
    by_cases hj' : j + 1 < n
    · rw [hinside i (j + 1) hj']
      cases i with
      | zero =>
        simp only [hrow, sub_zero, sub_nonneg]
        exact hanti (sub_nonneg.mpr (hle 0 j (Nat.zero_le _) hj))
          (sub_nonneg.mpr (hle 0 _ (Nat.zero_le _) hj'))
          (sub_le_sub_right (hle j _ (Nat.le_succ _) hj') _)
      | succ i =>
        rw [hinside i j hj, hinside i (j + 1) hj']
        have hr := convex_rectangle hf
          (sub_nonneg.mpr (hle (i + 1) j hij hj))
          (sub_nonneg.mpr (hle i (i + 1) (Nat.le_succ _) (hij.trans_lt hj)))
          (sub_nonneg.mpr (hle j (j + 1) (Nat.le_succ _) hj'))
        rw [show z j - z (i + 1) + (z (i + 1) - z i) = z j - z i by ring,
          show z j - z (i + 1) + (z (j + 1) - z j) = z (j + 1) - z (i + 1) by ring,
          show z j - z i + (z (j + 1) - z j) = z (j + 1) - z i by ring] at hr
        linarith
    · have he : j + 2 = n + 1 := by omega
      simp only [he, hcol, sub_zero]
      cases i with
      | zero =>
        rw [hrow, sub_zero]
        exact hn _ (sub_nonneg.mpr (hle 0 j (Nat.zero_le _) hj))
      | succ i =>
        rw [hinside i j hj, sub_nonneg]
        exact hanti (sub_nonneg.mpr (hle (i + 1) j hij hj))
          (sub_nonneg.mpr (hle i j (Nat.le_of_succ_le hij) hj))
          (sub_le_sub_left (hle i _ (Nat.le_succ _) (hij.trans_lt hj)) _)
  convert IntervalKernel.posSemidef_truncation (𝕜 := ℝ) A hrect using 1
  ext i j
  rcases le_total i j with h | h
  · have h' : i.val ≤ j.val := h
    simp only [Matrix.of_apply, min_eq_left h', max_eq_right h', min_eq_left (hmono h),
      max_eq_right (hmono h), hrow, hcol, sub_zero]
    rw [hinside _ _ j.isLt]
    simp [z, i.isLt, j.isLt]
  · have h' : j.val ≤ i.val := h
    simp only [Matrix.of_apply, min_eq_right h', max_eq_left h', min_eq_right (hmono h),
      max_eq_left (hmono h), hrow, hcol, sub_zero]
    rw [hinside _ _ i.isLt]
    simp [z, i.isLt, j.isLt]

/-- The geometric-sum profile of the normalized kernel at zero. -/
def zeroProfile (p : ℕ) (c : ℝ) : ℝ :=
  let q := Real.exp (-3 * c / (p : ℝ))
  let H := ∑ j ∈ Finset.range (p + 1), q ^ j
  let J := ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q ^ j
  (H - √(J - ((p + 2).choose 2 : ℝ) * Real.exp (-2 * c))) /
    ((p + 1 : ℝ) * Real.exp (-3 * c / 2))

private theorem homogeneousTwo_scale (p : ℕ) (q Y : ℝ) :
    homogeneousTwo p (q * Y) Y = Y ^ p * ∑ j ∈ Finset.range (p + 1), q ^ j := by
  simp only [homogeneousTwo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp hj)]
  ring

private theorem defect_zero_left (p : ℕ) (hp : 0 < p) (x y : ℝ) :
    defect p 0 x y = homogeneousTwo p (x ^ 3) (y ^ 3) := by
  rw [defect_eq_homogeneous]
  simp only [zero_pow (by decide : 3 ≠ 0), zero_mul, zero_pow hp.ne', mul_zero, sub_zero,
    homogeneousThree, Finset.sum_range_succ', pow_succ, mul_zero, zero_mul, Finset.sum_const_zero,
    pow_zero, one_mul, Nat.sub_zero, zero_add]

private theorem zero_weight (p : ℕ) (hp : 0 < p) (x : ℝ) :
    defect p 0 x x = (p + 1 : ℝ) * (x ^ 3) ^ p := by
  rw [defect_zero_left p hp]
  simpa [homogeneousTwo] using geom_sum₂_self (x ^ 3) (p + 1)

private theorem defect_zero_pair (p : ℕ) (hp : 0 < p) (y : ℝ) :
    defect p 0 0 y = (y ^ 3) ^ p := by
  rw [defect_zero_left p hp]
  simp only [zero_pow (by decide : 3 ≠ 0), homogeneousTwo, Finset.sum_range_succ', pow_succ,
    mul_zero, zero_mul, Finset.sum_const_zero, pow_zero, one_mul, Nat.sub_zero, zero_add]

private theorem homogeneousThree_repeat_scale (p : ℕ) (q Y : ℝ) :
    homogeneousThree p Y (q * Y) (q * Y) =
      Y ^ p * ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q ^ j := by
  unfold homogeneousThree
  rw [← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range_succ_iff.mp hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj']
  have hdiag : homogeneousTwo j (q * Y) (q * Y) = (j + 1 : ℝ) * (q * Y) ^ j := by
    simpa [homogeneousTwo] using geom_sum₂_self (q * Y) (j + 1)
  rw [hdiag, mul_pow]
  calc
    _ = Y ^ (p - j) * Y ^ j * ((j + 1 : ℝ) * q ^ j) := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hj']

/-- At positive roots, the normalized upper-triangular formula equals the explicit geometric-sum
profile evaluated at the scaled logarithmic gap. -/
theorem normalized_zero_eq_profile {p : ℕ} (hp : 0 < p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    normalized (fun t ↦ defect p 0 t t) (fun t ↦ defect p 0 t t) (defect p 0)
      (fun s t ↦ defect p 0 0 t * defect p s s t) x y =
    zeroProfile p ((p : ℝ) * (Real.log y - Real.log x)) := by
  let c := (p : ℝ) * (Real.log y - Real.log x)
  let q := Real.exp (-3 * c / (p : ℝ))
  let Y := y ^ 3
  let H := ∑ j ∈ Finset.range (p + 1), q ^ j
  let J := ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q ^ j
  let N := ((p + 2).choose 2 : ℝ)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq : q = (x / y) ^ 3 := by
    dsimp only [q, c]
    rw [show -3 * ((p : ℝ) * (Real.log y - Real.log x)) / (p : ℝ) =
      (3 : ℕ) * (Real.log x - Real.log y) by push_cast; field_simp; ring,
      Real.exp_nat_mul, Real.exp_sub, Real.exp_log hx, Real.exp_log hy]
  have hxq : x ^ 3 = q * Y := by rw [hq, div_pow]; exact (div_mul_cancel₀ _ (by positivity)).symm
  have hY : 0 < Y ^ p := by dsimp [Y]; positivity
  have hD : defect p 0 x y = Y ^ p * H := by
    rw [defect_zero_left p hp, hxq]
    exact homogeneousTwo_scale p q Y
  have hc : (x * x * y) ^ p = Y ^ p * Real.exp (-2 * c) := by
    have he : Real.exp (-2 * c) = ((x / y) ^ 2) ^ p := by
      rw [show -2 * c = (p : ℝ) * ((2 : ℕ) * (Real.log x - Real.log y)) by dsimp [c]; push_cast; ring,
        Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_sub, Real.exp_log hx, Real.exp_log hy]
    rw [he, ← mul_pow]
    congr 1
    dsimp [Y]
    field_simp
    <;> ring
  have hJ : defect p x x y = Y ^ p * (J - N * Real.exp (-2 * c)) := by
    rw [defect_cycle_all p y x x, defect_eq_homogeneous, hxq, show y * x * x = x * x * y by ring, hc]
    change homogeneousThree p Y (q * Y) (q * Y) - N * (Y ^ p * Real.exp (-2 * c)) = _
    rw [homogeneousThree_repeat_scale]
    dsimp only [J]
    ring
  have hrad : defect p 0 0 y * defect p x x y =
      (Y ^ p) ^ 2 * (J - N * Real.exp (-2 * c)) := by
    rw [defect_zero_pair p hp, hJ]
    change Y ^ p * (Y ^ p * _) = _
    ring
  have hpow : q ^ p = Real.exp (-3 * c) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hW : √(defect p 0 x x) * √(defect p 0 y y) =
      ((p + 1 : ℝ) * Y ^ p) * Real.exp (-3 * c / 2) := by
    rw [zero_weight p hp, zero_weight p hp, hxq, mul_pow, hpow, ← Real.sqrt_mul (by positivity)]
    change √(((p + 1 : ℝ) * (Real.exp (-3 * c) * Y ^ p)) * ((p + 1 : ℝ) * Y ^ p)) = _
    rw [show ((p + 1 : ℝ) * (Real.exp (-3 * c) * Y ^ p)) * ((p + 1 : ℝ) * Y ^ p) =
        (((p + 1 : ℝ) * Y ^ p) * Real.exp (-3 * c / 2)) ^ 2 by
          rw [mul_pow, ← Real.exp_nat_mul]
          push_cast
          rw [show (2 : ℝ) * (-3 * c / 2) = -3 * c by ring]
          ring,
      Real.sqrt_sq (by positivity)]
  rw [normalized, div_div, hD, hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hY.le, hW]
  change (Y ^ p * H - Y ^ p * √(J - N * Real.exp (-2 * c))) /
    (((p + 1 : ℝ) * Y ^ p) * Real.exp (-3 * c / 2)) =
      (H - √(J - N * Real.exp (-2 * c))) / ((p + 1 : ℝ) * Real.exp (-3 * c / 2))
  field_simp
  <;> ring

private theorem zeroProfile_continuous (p : ℕ) : Continuous (zeroProfile p) := by
  unfold zeroProfile
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro c
    positivity

private theorem zeroProfile_tendsto {p : ℕ} (hp : 0 < p) :
    Tendsto (zeroProfile p) atTop (𝓝 0) := by
  let q (c : ℝ) := Real.exp (-3 * c / (p : ℝ))
  let H (c : ℝ) := ∑ j ∈ Finset.range (p + 1), q c ^ j
  let J (c : ℝ) := ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q c ^ j
  let N := ((p + 2).choose 2 : ℝ)
  let R (c : ℝ) := J c - N * Real.exp (-2 * c)
  let B (c : ℝ) := (q c ^ (p + 1) + p - (p + 1 : ℝ) * q c) / (1 - q c)^2
  let k : ℝ := 1 + 3 / (p : ℝ)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have decay (a : ℝ) (ha : 0 < a) : Tendsto (fun c : ℝ ↦ Real.exp (-a * c)) atTop (𝓝 0) := by
    have ht : Tendsto (fun c : ℝ ↦ a * c) atTop atTop :=
      tendsto_id.const_mul_atTop ha
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
  have hq : Tendsto q atTop (𝓝 0) := by
    rw [show q = (fun c ↦ Real.exp (-(3 / (p : ℝ)) * c)) by
      funext c
      change Real.exp (-3 * c / (p : ℝ)) = _
      congr 1
      ring]
    exact decay _ (by positivity)
  have hHc : Continuous (fun u : ℝ ↦ ∑ j ∈ Finset.range (p + 1), u ^ j) := by fun_prop
  have hJc : Continuous (fun u : ℝ ↦ ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * u ^ j) := by
    fun_prop
  have hH0 : (∑ j ∈ Finset.range (p + 1), (0 : ℝ) ^ j) = 1 := by simp
  have hJ0 : (∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * (0 : ℝ) ^ j) = 1 := by
    rw [Finset.sum_range_succ']
    simp [pow_succ]
  have hH : Tendsto H atTop (𝓝 1) := by
    simpa only [Function.comp_def, hH0] using (hHc.continuousAt (x := 0)).tendsto.comp hq
  have hJ : Tendsto J atTop (𝓝 1) := by
    simpa only [Function.comp_def, hJ0] using (hJc.continuousAt (x := 0)).tendsto.comp hq
  have hR : Tendsto R atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using hJ.sub ((decay 2 (by norm_num)).const_mul N)
  have hsqrt : Tendsto (fun c ↦ √(R c)) atTop (𝓝 1) := by simpa using hR.sqrt
  have hBc : ContinuousAt (fun u : ℝ ↦ (u ^ (p + 1) + p - (p + 1 : ℝ) * u) / (1 - u)^2) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hB : Tendsto B atTop (𝓝 (p : ℝ)) := by
    simpa [Function.comp_def] using hBc.tendsto.comp hq
  have hD : Tendsto (fun c ↦ (p + 1 : ℝ) * (H c + √(R c))) atTop
      (𝓝 ((p + 1 : ℝ) * (1 + 1))) := (hH.add hsqrt).const_mul _
  have hE : Tendsto (fun c ↦ Real.exp (-c / 2)) atTop (𝓝 0) := by
    convert decay (1/2) (by norm_num) using 1
    ext c
    congr 1
    ring
  have hG : Tendsto (fun c ↦ Real.exp (-c / 2) *
      (N + Real.exp (-k * c) * B c) / ((p + 1 : ℝ) * (H c + √(R c)))) atTop (𝓝 0) := by
    have h := (hE.mul (((decay k (by dsimp [k]; positivity)).mul hB).const_add N)).div hD
      (by positivity : (p + 1 : ℝ) * (1 + 1) ≠ 0)
    change Tendsto (fun c ↦ Real.exp (-c / 2) *
      (N + Real.exp (-k * c) * B c) / ((p + 1 : ℝ) * (H c + √(R c)))) atTop
        (𝓝 (0 * (N + 0 * (p : ℝ)) / ((p + 1 : ℝ) * (1 + 1)))) at h
    simpa using h
  apply hG.congr'
  have hRpos := hR.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hRpos] with c hc hr
  have hq1 : q c < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hc) hp'
  have hne : 1 - q c ≠ 0 := (sub_pos.mpr hq1).ne'
  have hb : 0 < H c + √(R c) := by
    dsimp only [H]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ by dsimp [q]; positivity)
      (Real.sqrt_pos.mpr hr)
  have hgeom : (1 - q c) * H c = 1 - q c ^ (p + 1) := by
    dsimp only [H]
    linear_combination -(geom_sum_mul (q c) (p + 1))
  have hj : (1 - q c)^2 * J c =
      1 - (p + 2 : ℝ) * q c ^ (p + 1) + (p + 1 : ℝ) * q c ^ (p + 2) := by
    have hh := DividedDifference.clear_repeat_last p (1 : ℝ) (q c)
    rw [show homogeneousThree p 1 (q c) (q c) = J c by
      simpa [J] using homogeneousThree_repeat_scale p (q c) 1] at hh
    simp only [one_pow, mul_one] at hh
    linear_combination hh
  have hdiff : H c ^ 2 - J c = q c ^ (p + 1) * B c := by
    have hg2 := congrArg (fun x : ℝ ↦ x ^ 2) hgeom
    dsimp [B]
    field_simp [hne]
    rw [show p + 2 = p + 1 + 1 by omega, pow_succ] at hj
    linear_combination hg2 - hj
  have hz : q c ^ (p + 1) = Real.exp (-k * c) * Real.exp (-2 * c) := by
    dsimp [q, k]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hRational : (H c - √(R c)) * (H c + √(R c)) =
      Real.exp (-2 * c) * (N + Real.exp (-k * c) * B c) := by
    calc
      _ = H c ^ 2 - J c + N * Real.exp (-2 * c) := by
        rw [mul_comm (H c - √(R c)), ← sq_sub_sq, Real.sq_sqrt hr.le]
        dsimp [R]
        ring
      _ = _ := by rw [hdiff, hz]; ring
  have he : Real.exp (-c / 2) * Real.exp (-3 * c / 2) = Real.exp (-2 * c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change _ / ((p + 1 : ℝ) * (H c + √(R c))) =
    (H c - √(R c)) / ((p + 1 : ℝ) * Real.exp (-3 * c / 2))
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  linear_combination - (p + 1 : ℝ) * hRational +
    (p + 1 : ℝ) * (N + Real.exp (-k * c) * B c) * he

/-- A convex profile tending to zero gives the zero-centered PSD hypothesis of the
singular four-spectrum product bound. Convexity includes the endpoint at zero. -/
theorem zeroUpperPSD_of_convex_profile {p : ℕ} (hp : 0 < p)
    (hconv : ConvexOn ℝ (Ici 0) (zeroProfile p)) : ZeroUpperPSD.{u} p := by
  classical
  intro ι _ x hx
  let z (i : ι) := (p : ℝ) * Real.log (x i)
  let w (i : ι) := √(defect p 0 (x i) (x i))
  have hw (i : ι) : w i ≠ 0 := by
    dsimp [w]
    rw [zero_weight p hp]
    exact (Real.sqrt_pos.mpr (by positivity [hx i])).ne'
  have hp' : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have h := (profile_gram_posSemidef hconv (zeroProfile_tendsto hp) z).conjTranspose_mul_mul_same (Matrix.diagonal w)
  rw [diagonal_conjTranspose] at h
  convert h using 1
  ext i j
  simp only [diagonal_mul, mul_diagonal, Matrix.of_apply, star_trivial]
  rcases le_total (x i) (x j) with hij | hji
  · have hz : z i ≤ z j := mul_le_mul_of_nonneg_left (Real.log_le_log (hx i) hij) hp'
    rw [min_eq_left hz, max_eq_right hz, upperKernel, min_eq_left hij, max_eq_right hij]
    rw [show z j - z i = (p : ℝ) * (Real.log (x j) - Real.log (x i)) by dsimp [z]; ring,
      ← normalized_zero_eq_profile hp (hx i) (hx j)]
    change _ = w i * ((_ - _) / w i / w j) * w j
    field_simp [hw i, hw j]
  · have hz : z j ≤ z i := mul_le_mul_of_nonneg_left (Real.log_le_log (hx j) hji) hp'
    rw [min_eq_right hz, max_eq_left hz, upperKernel, min_eq_right hji, max_eq_left hji]
    rw [show z i - z j = (p : ℝ) * (Real.log (x i) - Real.log (x j)) by dsimp [z]; ring,
      ← normalized_zero_eq_profile hp (hx j) (hx i)]
    change _ = w i * ((_ - _) / w j / w i) * w j
    field_simp [hw i, hw j]
    <;> ring

private theorem zero_radicand_pos {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    0 < (∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * Real.exp (-3 * c / (p : ℝ)) ^ j) -
      ((p + 2).choose 2 : ℝ) * Real.exp (-2 * c) := by
  let x := Real.exp (-c / (p : ℝ))
  let q := Real.exp (-3 * c / (p : ℝ))
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hx : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hc) hp')
  have hxq : x ^ 3 = q := by
    dsimp [x, q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow : (x * x) ^ p = Real.exp (-2 * c) := by
    rw [← pow_two]
    dsimp [x]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hd := DimThree.defect_corner p (a := 1) (x := x) (y := x) zero_le_one hx.le hx.le
  have hne : √(defect p 1 1 x * defect p x x x) ≠ defect p 1 x x := by
    intro he
    rcases (DimThree.defect_corner_eq_iff p zero_le_one hx.le hx.le).mp he with hp0 | hx0
    · exact hp.ne' hp0
    · exact hx1.ne' hx0
  have hpos := (Real.sqrt_nonneg _).trans_lt (lt_of_le_of_ne hd hne)
  rw [defect_eq_homogeneous, one_pow, hxq, one_mul, hpow] at hpos
  rw [show homogeneousThree p (1 : ℝ) q q =
      ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q ^ j by
    simpa using homogeneousThree_repeat_scale p q 1] at hpos
  exact hpos

private theorem zeroProfile_contDiffOn {p : ℕ} (hp : 0 < p) :
    ContDiffOn ℝ 2 (zeroProfile p) (Ioi 0) := by
  unfold zeroProfile
  apply ContDiffOn.div
  · apply ContDiffOn.sub
    · fun_prop
    · apply ContDiffOn.sqrt
      · fun_prop
      · intro c hc
        exact (zero_radicand_pos hp hc).ne'
  · fun_prop
  · intro c _
    positivity

/-- Once the scalar second derivative is nonnegative, the zero-centered Gram matrix is PSD
at every finite positive sample. -/
theorem zeroUpperPSD_of_profile_curvature {p : ℕ} (hp : 0 < p)
    (hcurv : ∀ c : ℝ, 0 < c → 0 ≤ deriv^[2] (zeroProfile p) c) : ZeroUpperPSD.{u} p := by
  apply zeroUpperPSD_of_convex_profile hp
  refine convexOn_of_deriv2_nonneg (convex_Ici 0) (zeroProfile_continuous p).continuousOn ?_ ?_ ?_
  · rw [interior_Ici]
    exact (zeroProfile_contDiffOn hp).differentiableOn (by decide)
  · rw [interior_Ici]
    exact ((zeroProfile_contDiffOn hp).deriv_of_isOpen (m := 1) isOpen_Ioi (by decide)).differentiableOn
      (by decide)
  · rw [interior_Ici]
    exact hcurv

/-- The geometric-sum profile written with the reciprocal-degree radicand.
The positive gap ensures the geometric denominator is nonzero. -/
theorem zeroProfile_eq_rationalized {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    zeroProfile p c =
      let h : ℝ := 1 / p
      let d := 1 - Real.exp (-3*h*c)
      (1 - Real.exp (-3*(1+h)*c) - √(rationalizedRadicand c h)) /
        ((p + 1 : ℝ) * d * Real.exp (-3*c/2)) := by
  let h : ℝ := 1 / p
  let q := Real.exp (-3 * c / (p : ℝ))
  let d := 1 - q
  let H := ∑ j ∈ Finset.range (p + 1), q ^ j
  let J := ∑ j ∈ Finset.range (p + 1), (j + 1 : ℝ) * q ^ j
  let N := ((p + 2).choose 2 : ℝ)
  let R := J - N * Real.exp (-2*c)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) hc) hp')
  have hd : 0 < d := sub_pos.mpr hq1
  have hq : Real.exp (-3*h*c) = q := by
    dsimp [q, h]
    congr 1
    ring
  have hz : Real.exp (-3*(1+h)*c) = q ^ (p+1) := by
    dsimp [q, h]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    <;> ring
  have ha : (1+h)/h = (p+1 : ℝ) := by
    dsimp [h]
    field_simp
    <;> ring
  have hb : (1+2*h)/h = (p+2 : ℝ) := by
    dsimp [h]
    field_simp
    <;> ring
  have hN : N = (p+1 : ℝ) * (p+2 : ℝ) / 2 := by
    dsimp [N]
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hH : d * H = 1 - q ^ (p+1) := by
    dsimp [d, H]
    linear_combination -(geom_sum_mul q (p+1))
  have hJ : d^2 * J = 1 - (p+2 : ℝ) * q^(p+1) + (p+1 : ℝ) * q^(p+2) := by
    have hj := DividedDifference.clear_repeat_last p (1 : ℝ) q
    rw [show homogeneousThree p (1 : ℝ) q q = J by
      simpa [J] using homogeneousThree_repeat_scale p q 1] at hj
    simp only [one_pow, mul_one] at hj
    dsimp only [d]
    linear_combination hj
  have hR : rationalizedRadicand c h = d^2 * R := by
    unfold rationalizedRadicand
    rw [hq, hz, ha, hb]
    change 1 - q^(p+1) * (1 + (p+1 : ℝ) * d) -
        ((p+1 : ℝ)*d*((p+2 : ℝ)*d)/2) * Real.exp (-2*c) = d^2 * R
    dsimp only [R]
    rw [hN, mul_sub (d^2) J, hJ, show p+2 = p+1+1 by omega, pow_succ q (p+1)]
    dsimp only [d]
    ring
  change (H - √R) / ((p + 1 : ℝ) * Real.exp (-3*c/2)) =
    (1 - Real.exp (-3*(1+h)*c) - √(rationalizedRadicand c h)) /
      ((p + 1 : ℝ) * (1 - Real.exp (-3*h*c)) * Real.exp (-3*c/2))
  rw [hq, hz, hR, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le, ← hH]
  change (H - √R) / ((p + 1 : ℝ) * Real.exp (-3*c/2)) =
      (d*H - d*√R) / ((p + 1 : ℝ) * d * Real.exp (-3*c/2))
  field_simp
  <;> ring

/-- The stable profile on the positive logarithmic gaps. The formula uses the
sum of the two terms in the radical denominator. -/
theorem zeroProfile_eq_tail_formula {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    zeroProfile p c =
      let h : ℝ := 1 / p
      let d := 1 - Real.exp (-3*h*c)
      let a := (p+1 : ℝ) * d
      let b := (p+2 : ℝ) * d
      let v := 1 - Real.exp (-3*(1+h)*c)
      Real.exp (-c/2) *
        ((b/2 + Real.exp (-(1+3*h)*c) * (1-v/a)) / (v + √(rationalizedRadicand c h))) := by
  let h : ℝ := 1 / p
  let d := 1 - Real.exp (-3*h*c)
  let a := (p+1 : ℝ) * d
  let b := (p+2 : ℝ) * d
  let z := Real.exp (-3*(1+h)*c)
  let v := 1 - z
  let S := rationalizedRadicand c h
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hzero : (p : ℝ) ≠ 0 := hp'.ne'
  have hd : 0 < d := by
    apply sub_pos.mpr (Real.exp_lt_one_iff.mpr ?_)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hh) hc
  have ha : 0 < a := by dsimp [a]; positivity
  have hv : 0 < v := by
    apply sub_pos.mpr (Real.exp_lt_one_iff.mpr ?_)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by positivity)) hc
  have hS : 0 ≤ S := by
    apply nonneg_of_mul_nonneg_right _ (Real.exp_pos ((3+6*h)*c))
    exact (by positivity : 0 ≤ 27 * (1+h) * (1+2*h) * (1+3*h) * c^4 / 24).trans
      (rationalized_radicand_lower hc.le hh)
  have ha' : (1+h)/h = (p+1 : ℝ) := by dsimp [h]; field_simp
  have hb' : (1+2*h)/h = (p+2 : ℝ) := by dsimp [h]; field_simp
  have hS' : S = 1 - z*(1+a) - a*b/2 * Real.exp (-2*c) := by
    dsimp only [S, rationalizedRadicand]
    rw [ha', hb']
  have hmul : (v-√S) * (v+√S) = z*(a-v) + a*b/2 * Real.exp (-2*c) := by
    rw [mul_comm (v-√S), ← sq_sub_sq, Real.sq_sqrt hS, hS']
    dsimp only [v]
    ring
  let E := Real.exp (-c/2)
  let D := Real.exp (-3*c/2)
  let u := Real.exp (-(1+3*h)*c)
  have hED : E * D = Real.exp (-2*c) := by
    dsimp [E, D]
    rw [← Real.exp_add]
    congr 1
    ring
  have hz : z = u * Real.exp (-2*c) := by
    dsimp [z, u]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [zeroProfile_eq_rationalized hp hc]
  change (v-√S) / (a*D) = E * ((b/2+u*(1-v/a))/(v+√S))
  have hD : 0 < D := Real.exp_pos _
  have hvD : 0 < v+√S := add_pos_of_pos_of_nonneg hv (Real.sqrt_nonneg _)
  rw [← mul_div_assoc]
  apply (div_eq_div_iff (mul_ne_zero ha.ne' hD.ne') hvD.ne').mpr
  rw [hmul, hz, ← hED]
  field_simp [ha.ne']
  <;> ring

#print axioms zeroProfile_eq_tail_formula
#print axioms zeroProfile_eq_rationalized
#print axioms zeroUpperPSD_of_profile_curvature
#print axioms zeroProfile_tendsto
#print axioms zeroProfile_continuous
#print axioms normalized_zero_eq_profile
#print axioms zeroUpperPSD_of_convex_profile

end RefinedBMV.FourSpectrumLift
