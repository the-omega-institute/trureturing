/- GID: D5/S3/Quantum/Hiai/SpectralNonconcavityScalars
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/SpectralNonconcavityScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real root, scale and finite-factor estimates consumed by the UNTILDE matrix obstruction. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Hiai.SpectralNonconcavity

open Filter Topology

def radius (u v w : ℝ) : ℝ := Real.sqrt (((u - w) / 2) ^ (2 : ℕ) + v ^ (2 : ℕ))
def lowerRoot (u v w : ℝ) : ℝ := (u + w) / 2 - radius u v w
def upperRoot (u v w : ℝ) : ℝ := (u + w) / 2 + radius u v w

lemma root_algebra (u v w : ℝ) (hv : 0 < v) :
    0 < radius u v w ∧
    lowerRoot u v w < upperRoot u v w ∧
    upperRoot u v w * lowerRoot u v w = u * w - v ^ (2 : ℕ) := by
  have hr : 0 < ((u - w) / 2) ^ (2 : ℕ) + v ^ (2 : ℕ) := by positivity
  have hr2 := Real.sq_sqrt hr.le
  have hrp : 0 < radius u v w := Real.sqrt_pos.mpr hr
  refine ⟨hrp, ?_, ?_⟩
  · dsimp [lowerRoot, upperRoot]
    linarith
  · dsimp [upperRoot, lowerRoot, radius] at *
    nlinarith

lemma scaled_upperRoot (z u v w : ℝ) (hz : 0 ≤ z) :
    z * upperRoot u v w = upperRoot (z * u) (z * v) (z * w) := by
  have he : (((z * u - z * w) / 2) ^ (2 : ℕ) + (z * v) ^ (2 : ℕ)) =
      z ^ (2 : ℕ) * (((u - w) / 2) ^ (2 : ℕ) + v ^ (2 : ℕ)) := by ring
  dsimp [upperRoot, radius]
  rw [he, Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq hz]
  ring

lemma slope_factor (M m z c α : ℝ) (hM : 0 < M) (hm : 0 < m)
    (hz : 0 < z) (hc : c = z * M) (hne : m ≠ M) :
    (M ^ α - m ^ α) / (M - m) =
      c ^ (α - 1) * z ^ (1 - α) * (1 - (m / M) ^ α) / (1 - m / M) := by
  rw [hc, Real.mul_rpow hz.le hM.le, Real.div_rpow hm.le hM.le]
  have hzpow : z ^ (α - 1) * z ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hz]
    simp
  have hMpow : M ^ (α - 1) = M ^ α / M := by
    rw [Real.rpow_sub hM, Real.rpow_one]
  rw [hMpow]
  have he : z ^ (α - 1) * (M ^ α / M) * z ^ (1 - α) = M ^ α / M := by
    calc
      _ = (z ^ (α - 1) * z ^ (1 - α)) * (M ^ α / M) := by ring
      _ = _ := by rw [hzpow, one_mul]
  rw [he]
  field_simp [hM.ne', (Real.rpow_pos_of_pos hM α).ne', sub_ne_zero.mpr hne.symm]

def interior (α p : ℝ) : ℝ :=
  min (1 / 4) (((2 : ℝ) ^ (-α / (1 - α)) - 1 / 2) ^ (1 / p))

lemma interior_gap (α p : ℝ) (hα : 0 < α) (hαh : α < 1 / 2) (hp : 0 < p) :
    0 < interior α p ∧ interior α p ≤ 1 / 4 ∧
      (((1 - interior α p) ^ p + interior α p ^ p) / 2) ^ ((1 - α) / p) <
        (2 : ℝ) ^ (-α / p) := by
  let h := (2 : ℝ) ^ (-α / (1 - α))
  have hr : 0 < 1 - α := by linarith
  have hex : (-1 : ℝ) < -α / (1 - α) := by
    apply (lt_div_iff₀ hr).2
    linarith
  have hh0 : 1 / 2 < h := by
    have he := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hex
    norm_num at he
    exact he
  have hh1 : h < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    apply div_neg_of_neg_of_pos
    · linarith
    · exact hr)
  have hτ0 : 0 < interior α p := lt_min (by norm_num)
    (Real.rpow_pos_of_pos (by dsimp [h] at hh0; linarith) _)
  have hτ1 : interior α p ≤ 1 / 4 := min_le_left _ _
  have hτ2 : interior α p ^ p ≤ h - 1 / 2 := by
    have hl := Real.rpow_le_rpow hτ0.le
      (min_le_right (1 / 4 : ℝ) ((h - 1 / 2) ^ (1 / p))) hp.le
    have he : ((h - 1 / 2) ^ (1 / p)) ^ p = h - 1 / 2 := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ h - 1 / 2)]
      rw [show 1 / p * p = (1 : ℝ) by field_simp]
      rw [Real.rpow_one]
    exact he ▸ hl
  have hτlt : interior α p < 1 := by linarith
  have hb : (1 - interior α p) ^ p < 1 :=
    Real.rpow_lt_one (by linarith) (by linarith) hp
  have hm : ((1 - interior α p) ^ p + interior α p ^ p) / 2 < h := by linarith
  have hc := Real.rpow_lt_rpow (by positivity :
    0 ≤ ((1 - interior α p) ^ p + interior α p ^ p) / 2) hm
    (show 0 < (1 - α) / p by positivity)
  have he : h ^ ((1 - α) / p) = (2 : ℝ) ^ (-α / p) := by
    dsimp [h]
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  exact ⟨hτ0, hτ1, he ▸ hc⟩

def scale (p s : ℝ) : ℝ := s ^ (p / 2)
def entryX (p s : ℝ) : ℝ := (1 - s ^ (2 : ℕ)) ^ p
def entryA (p s : ℝ) : ℝ := ((1 - s) ^ p + scale p s ^ (2 : ℕ)) / 2
def entryB (p s : ℝ) : ℝ := ((1 - s) ^ p - scale p s ^ (2 : ℕ)) / 2
def entryE (p s : ℝ) : ℝ := ((1 - s ^ (2 : ℕ)) * (1 - s)) ^ (p / 2)
def entryC (p s : ℝ) : ℝ :=
  Real.sqrt (entryA p s * (entryX p s + scale p s ^ (4 : ℕ)) + 2 * scale p s ^ (3 : ℕ) * entryE p s)
def entryU (p s : ℝ) : ℝ :=
  (entryA p s + scale p s ^ (3 : ℕ) * entryE p s / entryX p s) / entryC p s
def entryV (p s : ℝ) : ℝ := entryB p s / entryC p s
def entryW (p s : ℝ) : ℝ :=
  (entryA p s + entryE p s / scale p s) / entryC p s
def scaledW (p s : ℝ) : ℝ :=
  (scale p s * entryA p s + entryE p s) / entryC p s
def largeScale (p s : ℝ) : ℝ :=
  upperRoot (scale p s * entryU p s) (scale p s * entryV p s) (scaledW p s)
def small (p s : ℝ) : ℝ := entryE p s / (entryX p s * largeScale p s)
def ratio (p s : ℝ) : ℝ := scale p s * small p s / largeScale p s
def slope (α p s : ℝ) : ℝ :=
  largeScale p s ^ (α - 1) * scale p s ^ (1 - α) *
    (1 - ratio p s ^ α) / (1 - ratio p s)

lemma scale_square (p s : ℝ) (hs : 0 ≤ s) : scale p s ^ (2 : ℕ) = s ^ p := by
  dsimp [scale]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  congr 1
  ring

lemma scale_fourth (p s : ℝ) (hs : 0 ≤ s) : scale p s ^ (4 : ℕ) = (s ^ (2 : ℕ)) ^ p := by
  dsimp [scale]
  rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hs,
    ← Real.rpow_natCast s 2, ← Real.rpow_mul hs]
  congr 1
  ring

lemma entry_facts (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    0 < scale p s ∧ 0 < entryX p s ∧ 0 < entryA p s ∧ 0 < entryB p s ∧
    0 < entryE p s ∧ 0 < entryC p s ∧
    entryE p s ^ (2 : ℕ) = entryX p s * (1 - s) ^ p ∧
    entryA p s ^ (2 : ℕ) - entryB p s ^ (2 : ℕ) = (1 - s) ^ p * scale p s ^ (2 : ℕ) ∧
    entryC p s ^ (2 : ℕ) = entryA p s * (entryX p s + scale p s ^ (4 : ℕ)) +
      2 * scale p s ^ (3 : ℕ) * entryE p s := by
  have ht : 0 < 1 - s ^ (2 : ℕ) := by nlinarith
  have h1s : 0 < 1 - s := by linarith
  have hz : 0 < scale p s := Real.rpow_pos_of_pos hs _
  have hx : 0 < entryX p s := Real.rpow_pos_of_pos ht _
  have ha : 0 < entryA p s := by dsimp [entryA]; positivity
  have hb : 0 < entryB p s := by
    dsimp [entryB]
    rw [scale_square p s hs.le]
    have h := Real.rpow_lt_rpow hs.le (show s < 1 - s by linarith) hp
    linarith
  have he : 0 < entryE p s := Real.rpow_pos_of_pos (mul_pos ht h1s) _
  have hrad : 0 < entryA p s * (entryX p s + scale p s ^ (4 : ℕ)) +
      2 * scale p s ^ (3 : ℕ) * entryE p s := by positivity
  have hc : 0 < entryC p s := Real.sqrt_pos.mpr hrad
  refine ⟨hz, hx, ha, hb, he, hc, ?_, ?_, Real.sq_sqrt hrad.le⟩
  · dsimp [entryE, entryX]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (mul_pos ht h1s).le]
    norm_num only [Nat.cast_ofNat]
    rw [show p / 2 * (2 : ℝ) = p by ring, Real.mul_rpow ht.le h1s.le]
  · dsimp [entryA, entryB]
    ring

def k : ℝ := Real.sqrt (1 / 2)
private lemma k_pos : 0 < k := Real.sqrt_pos.mpr (by norm_num)

lemma small_interval : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ s < 1 / 2 := by
  have h0 : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  have h1 : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  exact h0.and h1

lemma entry_limits (p : ℝ) (hp : 0 < p) :
    Tendsto (scale p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (entryX p) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (entryE p) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (entryC p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (entryU p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (entryV p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (scaledW p) (𝓝[>] 0) (𝓝 (1 / k)) := by
  have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have hz : Tendsto (scale p) (𝓝[>] 0) (𝓝 0) :=
    hid.rpow_const_nhds_zero (by positivity : 0 < p / 2)
  have hs : Tendsto (fun s : ℝ ↦ (1 - s) ^ p) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hone.sub hid).rpow_const (Or.inr hp.le)
  have hx : Tendsto (entryX p) (𝓝[>] 0) (𝓝 1) := by
    unfold entryX
    simpa [entryX] using (hone.sub (hid.pow 2)).rpow_const (Or.inr hp.le)
  have he : Tendsto (entryE p) (𝓝[>] 0) (𝓝 1) := by
    unfold entryE
    simpa [entryE] using ((hone.sub (hid.pow 2)).mul
      (hone.sub hid)).rpow_const (Or.inr (by positivity : 0 ≤ p / 2))
  have ha : Tendsto (entryA p) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    unfold entryA
    simpa [entryA] using (hs.add (hz.pow 2)).div_const 2
  have hb : Tendsto (entryB p) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    unfold entryB
    simpa [entryB] using (hs.sub (hz.pow 2)).div_const 2
  have hc : Tendsto (entryC p) (𝓝[>] 0) (𝓝 k) := by
    unfold entryC
    simpa [entryC, k] using ((ha.mul (hx.add (hz.pow 4))).add
      ((tendsto_const_nhds.mul (hz.pow 3)).mul he)).sqrt
  have hk : (1 / 2 : ℝ) / k = k := by
    apply (div_eq_iff k_pos.ne').2
    simpa only [k, ← sq] using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
  have hu : Tendsto (entryU p) (𝓝[>] 0) (𝓝 k) := by
    have h := (ha.add (((hz.pow 3).mul he).div hx (by norm_num))).div hc k_pos.ne'
    change Tendsto (fun s ↦ (entryA p s + scale p s ^ (3 : ℕ) * entryE p s / entryX p s) /
      entryC p s) (𝓝[>] 0) (𝓝 ((1 / 2 + 0 ^ (3 : ℕ) * 1 / 1) / k)) at h
    norm_num only [zero_pow, zero_mul, zero_div, add_zero] at h
    rw [hk] at h
    unfold entryU
    exact h
  have hv : Tendsto (entryV p) (𝓝[>] 0) (𝓝 k) := by
    have h := hb.div hc k_pos.ne'
    change Tendsto (fun s ↦ entryB p s / entryC p s) (𝓝[>] 0) (𝓝 ((1 / 2) / k)) at h
    rw [hk] at h
    exact h
  have hw : Tendsto (scaledW p) (𝓝[>] 0) (𝓝 (1 / k)) := by
    have h := ((hz.mul ha).add he).div hc k_pos.ne'
    change Tendsto (fun s ↦ (scale p s * entryA p s + entryE p s) / entryC p s)
      (𝓝[>] 0) (𝓝 ((0 * (1 / 2) + 1) / k)) at h
    simp only [zero_mul, zero_add] at h
    unfold scaledW
    exact h
  exact ⟨hz, hx, he, hc, hu, hv, hw⟩

private lemma upperRoot_zero (w : ℝ) (hw : 0 ≤ w) : upperRoot 0 0 w = w := by
  dsimp [upperRoot, radius]
  norm_num only [zero_add, zero_sub, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) (by norm_num))]
  ring

lemma finite_factor_limits (α p : ℝ) (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    Tendsto (largeScale p) (𝓝[>] 0) (𝓝 (1 / k)) ∧
    Tendsto (small p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (ratio p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (slope α p) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hz, hx, he, hc, hu, hv, hw⟩ := entry_limits p hp
  have hk := k_pos
  have hzu : Tendsto (fun s ↦ scale p s * entryU p s) (𝓝[>] 0) (𝓝 0) := by
    simpa using hz.mul hu
  have hzv : Tendsto (fun s ↦ scale p s * entryV p s) (𝓝[>] 0) (𝓝 0) := by
    simpa using hz.mul hv
  have hl : Tendsto (largeScale p) (𝓝[>] 0) (𝓝 (1 / k)) := by
    have h := ((hzu.add hw).div_const 2).add
      ((((hzu.sub hw).div_const 2).pow 2).add (hzv.pow 2)).sqrt
    change Tendsto (largeScale p) (𝓝[>] 0) (𝓝 (upperRoot 0 0 (1 / k))) at h
    rw [upperRoot_zero _ (by positivity)] at h
    exact h
  have hm : Tendsto (small p) (𝓝[>] 0) (𝓝 k) := by
    have h := he.div (hx.mul hl) (by positivity : (1 : ℝ) * (1 / k) ≠ 0)
    change Tendsto (fun s ↦ entryE p s / (entryX p s * largeScale p s))
      (𝓝[>] 0) (𝓝 (1 / (1 * (1 / k)))) at h
    simp only [one_mul, one_div_one_div] at h
    unfold small
    exact h
  have hq : Tendsto (ratio p) (𝓝[>] 0) (𝓝 0) := by
    have h := (hz.mul hm).div hl (by positivity : (1 / k : ℝ) ≠ 0)
    change Tendsto (fun s ↦ scale p s * small p s / largeScale p s)
      (𝓝[>] 0) (𝓝 (0 * k / (1 / k))) at h
    simp only [zero_mul, zero_div] at h
    unfold ratio
    exact h
  have hg : Tendsto (slope α p) (𝓝[>] 0) (𝓝 0) := by
    have hc' := hl.rpow_const (Or.inl (by positivity : (1 / k : ℝ) ≠ 0)) (p := α - 1)
    have hz' := hz.rpow_const_nhds_zero (show 0 < 1 - α by linarith)
    have hq' := hq.rpow_const_nhds_zero hα
    have h := ((hc'.mul hz').mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hq')).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hq) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun s ↦ largeScale p s ^ (α - 1) * scale p s ^ (1 - α) *
      (1 - ratio p s ^ α) / (1 - ratio p s)) (𝓝[>] 0)
      (𝓝 ((1 / k) ^ (α - 1) * 0 * (1 - 0) / (1 - 0))) at h
    simp only [mul_zero, zero_mul, zero_div] at h
    unfold slope
    exact h
  exact ⟨hl, hm, hq, hg⟩

lemma k_square_power (α : ℝ) : k ^ α * k ^ α = (2 : ℝ) ^ (-α) := by
  rw [← Real.rpow_add k_pos]
  dsimp [k]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

end D5.S3.Quantum.Hiai.SpectralNonconcavity
