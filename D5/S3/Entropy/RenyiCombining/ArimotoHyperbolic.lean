/- GID: D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/ArimotoHyperbolic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hyperbolic elasticity certificate for the binary Arimoto coordinate. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.LinearCombination

/-! Parameter comparison and an exact half-order elasticity certificate. -/

open Set

noncomputable section
namespace D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic

/-- The elasticity after the change of variable t = tanh s. -/
def elasticity (b s : ℝ) : ℝ :=
  b * Real.sinh s * Real.cosh s ^ 2 /
    (Real.sinh (b * s) * Real.cosh ((b + 1) * s))

def f (s r : ℝ) : ℝ := r * Real.cosh (r * s) / Real.sinh (r * s)
def g (s r : ℝ) : ℝ := r * Real.sinh (r * s) / Real.cosh (r * s)
private def L (b s : ℝ) : ℝ :=
  Real.cosh s / Real.sinh s + 2 * Real.sinh s / Real.cosh s - f s b - g s (b + 1)

lemma sinh_cosh_sub_pos {z : ℝ} (hz : 0 < z) :
    0 < Real.sinh z * Real.cosh z - z := by
  have h := Real.self_lt_sinh_iff.mpr (show 0 < 2 * z by linarith)
  rw [Real.sinh_two_mul] at h
  linarith

lemma f_hasDerivAt {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    HasDerivAt (f s)
      ((Real.sinh (r * s) * Real.cosh (r * s) - r * s) /
        Real.sinh (r * s) ^ 2) r := by
  have hn := (Real.sinh_pos_iff.mpr (mul_pos hr hs)).ne'
  have hd := ((hasDerivAt_id r).mul
    ((hasDerivAt_id r).mul_const s).cosh).div
    ((hasDerivAt_id r).mul_const s).sinh hn
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    linear_combination (r * s) * Real.cosh_sq_sub_sinh_sq (r * s)

private lemma g_hasDerivAt (s r : ℝ) :
    HasDerivAt (g s)
      (Real.sinh (r * s) / Real.cosh (r * s) + r * s / Real.cosh (r * s) ^ 2) r := by
  have hd := ((hasDerivAt_id r).mul
    ((hasDerivAt_id r).mul_const s).sinh).div
    ((hasDerivAt_id r).mul_const s).cosh
    (Real.cosh_pos (r * s)).ne'
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    linear_combination -(r * s) * Real.cosh_sq_sub_sinh_sq (r * s)

private lemma f_strictMonoOn {s : ℝ} (hs : 0 < s) : StrictMonoOn (f s) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
    (fun r hr => (f_hasDerivAt hs hr).continuousAt.continuousWithinAt)
  intro r hr
  have hr' : 0 < r := interior_subset hr
  rw [(f_hasDerivAt hs hr').deriv]
  exact div_pos (sinh_cosh_sub_pos (mul_pos hr' hs))
    (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos hr' hs)))

lemma g_strictMonoOn {s : ℝ} (hs : 0 < s) : StrictMonoOn (g s) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
    (fun r _ => (g_hasDerivAt s r).continuousAt.continuousWithinAt)
  intro r hr
  have hr' : 0 < r := interior_subset hr
  rw [(g_hasDerivAt s r).deriv]
  exact add_pos (div_pos (Real.sinh_pos_iff.mpr (mul_pos hr' hs)) (Real.cosh_pos _))
    (div_pos (mul_pos hr' hs) (sq_pos_of_pos (Real.cosh_pos _)))

private lemma f_neg (s r : ℝ) : f s (-r) = f s r := by
  simp [f, neg_mul, Real.cosh_neg, Real.sinh_neg]

private lemma elasticity_pos {b s : ℝ} (hs : 0 < s) (hb : b ≠ 0) :
    0 < elasticity b s := by
  have hc := Real.cosh_pos ((b + 1) * s)
  have hp := mul_pos (Real.sinh_pos_iff.mpr hs) (sq_pos_of_pos (Real.cosh_pos s))
  rcases lt_or_gt_of_ne hb with hb | hb
  · exact div_pos_of_neg_of_neg (by change b * Real.sinh s * Real.cosh s ^ 2 < 0; nlinarith [mul_neg_of_neg_of_pos hb hp])
      (mul_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr (mul_neg_of_neg_of_pos hb hs)) hc)
  · exact div_pos (by change 0 < b * Real.sinh s * Real.cosh s ^ 2; nlinarith [mul_pos hb hp])
      (mul_pos (Real.sinh_pos_iff.mpr (mul_pos hb hs)) hc)

private lemma elasticity_hasDerivAt {b s : ℝ} (hs : 0 < s) (hb : b ≠ 0) :
    HasDerivAt (elasticity b) (elasticity b s * L b s) s := by
  have hn : Real.sinh (b * s) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero hb hs.ne'
  have hd := (((Real.hasDerivAt_sinh s).const_mul b).mul
      ((Real.hasDerivAt_cosh s).pow 2)).div
    (((hasDerivAt_id s).const_mul b).sinh.mul
      ((hasDerivAt_id s).const_mul (b + 1)).cosh)
    (mul_ne_zero hn (Real.cosh_pos _).ne')
  convert hd using 1
  · rfl
  · dsimp [elasticity, L, f, g]
    field_simp [hn, (Real.cosh_pos s).ne', (Real.sinh_pos_iff.mpr hs).ne',
      (Real.cosh_pos ((b + 1) * s)).ne']
    <;> ring

private lemma half_identity (s : ℝ) :
    Real.cosh (3 / 2 * s) = Real.cosh (s / 2) * (2 * Real.cosh s - 1) := by
  have h₁ := Real.cosh_sq_sub_sinh_sq (s / 2)
  have h₂ := Real.cosh_two_mul (s / 2)
  have h₃ := Real.sinh_two_mul (s / 2)
  have h₄ := Real.cosh_add s (s / 2)
  rw [show (2 : ℝ) * (s / 2) = s by ring] at h₂ h₃
  rw [show s + s / 2 = (3 : ℝ) / 2 * s by ring] at h₄
  rw [h₄, h₃]
  linear_combination -Real.cosh (s / 2) * (h₂ + h₁)

private lemma elasticity_half {s : ℝ} (hs : 0 < s) :
    elasticity (1 / 2) s = Real.cosh s ^ 2 / (2 * Real.cosh s - 1) := by
  have hh := Real.sinh_two_mul (s / 2)
  rw [show (2 : ℝ) * (s / 2) = s by ring] at hh
  unfold elasticity
  rw [show ((1 : ℝ) / 2 + 1) * s = 3 / 2 * s by ring, half_identity,
    show (1 : ℝ) / 2 * s = s / 2 by ring, hh]
  have hn := (Real.sinh_pos_iff.mpr (show 0 < s / 2 by linarith)).ne'
  field_simp [hn, (Real.cosh_pos (s / 2)).ne']
  <;> ring

private lemma L_half_pos {s : ℝ} (hs : 0 < s) : 0 < L (1 / 2) s := by
  have hc : 1 < Real.cosh s := Real.one_lt_cosh.mpr hs.ne'
  have hn : 2 * Real.cosh s - 1 ≠ 0 := by linarith
  have hd := ((Real.hasDerivAt_cosh s).pow 2).div
    (((Real.hasDerivAt_cosh s).const_mul 2).sub_const 1) hn
  have he : HasDerivAt (elasticity (1 / 2))
      (2 * Real.cosh s * (Real.cosh s - 1) * Real.sinh s /
        (2 * Real.cosh s - 1) ^ 2) s := by
    have hd' := hd.congr_of_eventuallyEq (show
        elasticity (1 / 2) =ᶠ[nhds s]
          (fun z => Real.cosh z ^ 2 / (2 * Real.cosh z - 1)) from by
      filter_upwards [Ioi_mem_nhds hs] with z hz
      exact elasticity_half hz)
    convert hd' using 1 <;> dsimp <;> ring
  have hmul := (elasticity_hasDerivAt hs (by norm_num : (1 / 2 : ℝ) ≠ 0)).unique he
  have hp : 0 < 2 * Real.cosh s * (Real.cosh s - 1) * Real.sinh s /
        (2 * Real.cosh s - 1) ^ 2 :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (Real.cosh_pos s)) (by linarith))
      (Real.sinh_pos_iff.mpr hs)) (sq_pos_of_ne_zero hn)
  have hE := elasticity_pos hs (by norm_num : (1 / 2 : ℝ) ≠ 0)
  nlinarith

private lemma L_pos {b s : ℝ} (hs : 0 < s)
    (hb : (-1 < b ∧ b < 0) ∨ (0 < b ∧ b ≤ 1 / 2)) : 0 < L b s := by
  have hf := f_strictMonoOn hs
  have hg := g_strictMonoOn hs
  rcases hb with hb | hb
  · have hbf : f s (-b) < f s 1 := hf (show 0 < -b by linarith [hb.2]) (show (0 : ℝ) < 1 by norm_num) (by linarith [hb.1])
    have hbg : g s (b + 1) < g s 1 := hg (show 0 < b + 1 by linarith [hb.1]) (show (0 : ℝ) < 1 by norm_num) (by linarith [hb.2])
    have hg1 : 0 < g s 1 := by
      simpa [g] using div_pos (Real.sinh_pos_iff.mpr hs) (Real.cosh_pos s)
    rw [f_neg] at hbf
    simp only [f, g, one_mul] at hbf hbg hg1
    dsimp [L, f, g]
    simp only [mul_div_assoc] at *
    linarith
  · have hbf : f s b ≤ f s (1 / 2) := hf.monotoneOn hb.1 (by norm_num) hb.2
    have hbg : g s (b + 1) ≤ g s (1 / 2 + 1) :=
      hg.monotoneOn (show 0 < b + 1 by linarith [hb.1]) (show (0 : ℝ) < 1 / 2 + 1 by norm_num) (by linarith [hb.2])
    have hh := L_half_pos hs
    dsimp [L] at *
    linarith

/-- The Arimoto elasticity increases throughout both claimed order ranges. -/
theorem strictMonoOn_elasticity {b : ℝ}
    (hb : (-1 < b ∧ b < 0) ∨ (0 < b ∧ b ≤ 1 / 2)) :
    StrictMonoOn (elasticity b) (Ioi 0) := by
  have hn : b ≠ 0 := by rcases hb with hb | hb <;> linarith
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
    (fun s hs => (elasticity_hasDerivAt hs hn).continuousAt.continuousWithinAt)
  intro s hs
  have hs' : 0 < s := interior_subset hs
  rw [(elasticity_hasDerivAt hs' hn).deriv]
  exact mul_pos (elasticity_pos hs' hn) (L_pos hs' hb)

end D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
