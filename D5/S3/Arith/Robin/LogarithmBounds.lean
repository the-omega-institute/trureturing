/- GID: D5/S3/Arith/Robin/LogarithmBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/LogarithmBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict log-log tangency, logarithmic window estimates and a quadratic tail bound. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source for neg_log_one_sub_le: mlgraham/lean-eval-klartag-submission,
   commit 270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.MellinWeightedVariation

namespace D5.S3.Arith.Robin.RestrictedDivisorStrictInventory

local notation "price" => D5.S3.Arith.Robin.ActualRobinClockCovariance.g

theorem loglog_tangent {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hne : x ≠ y) :
    Real.log (Real.log y) - Real.log (Real.log x) < (y-x) * price x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx := Real.log_pos hx
  have hly := Real.log_pos hy
  have hlogne : Real.log y ≠ Real.log x := by
    intro he
    exact hne (Real.strictMonoOn_log.injOn hx0 hy0 he.symm)
  have hratio : Real.log y / Real.log x ≠ 1 := by
    intro he
    exact hlogne ((div_eq_one_iff_eq hlx.ne').mp he)
  have houter := Real.log_lt_sub_one_of_pos (div_pos hly hlx) hratio
  rw [Real.log_div hly.ne' hlx.ne'] at houter
  have hinner := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hinner
  have hnorm : Real.log y / Real.log x - 1 =
      (Real.log y - Real.log x) / Real.log x := by field_simp
  rw [hnorm] at houter
  calc
    _ < (Real.log y-Real.log x)/Real.log x := houter
    _ ≤ (y/x-1)/Real.log x := div_le_div_of_nonneg_right hinner hlx.le
    _ = (y-x) * price x := by
      unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
      field_simp

end D5.S3.Arith.Robin.RestrictedDivisorStrictInventory

namespace D5.S3.Arith.Lattices.Klartag

open Set Real

/-- **The sharp bound.**  `-log(1-x) ≤ x + x²` for `0 ≤ x ≤ 1/2`.

This is the step that fixes the `1/8`.  The crude `-log(1-x) ≤ 2x`, also true on `[0,1/2]`, would
put `γ = 1/2` and destroy the `n²`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + x ^ 2 := by
  have hle : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) (1 / 2) →
      0 ≤ Real.log (1 - z) + z + z ^ 2 := by
    set f : ℝ → ℝ := fun z => Real.log (1 - z) + z + z ^ 2 with hfdef
    set g : ℝ → ℝ := fun z => z * (1 - 2 * z) / (1 - z) with hgdef
    have hderiv : ∀ z : ℝ, z < 1 → HasDerivAt f (g z) z := by
      intro z hz
      have h1z : (1 : ℝ) - z ≠ 0 := by linarith
      have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub 1
      have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - z)⁻¹ * (-1)) z :=
        (Real.hasDerivAt_log h1z).comp z hlin
      have hid : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z)
      have hsum : HasDerivAt f ((1 - z)⁻¹ * (-1) + 1 + 2 * z) z := (hlog.add hid).add hsq
      have heq : (1 - z)⁻¹ * (-1) + 1 + 2 * z = g z := by
        rw [hgdef]; field_simp; ring
      rwa [heq] at hsum
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
      refine ContinuousOn.add (ContinuousOn.add ?_ continuousOn_id) (by fun_prop)
      refine Real.continuousOn_log.comp (by fun_prop) ?_
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := hz.2
      intro hcon
      simp only [sub_eq_zero] at hcon
      linarith [hz.2, hcon]
    have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Icc 0 (1 / 2)) hcont
      · intro z hz
        rw [interior_Icc] at hz
        exact (hderiv z (by linarith [hz.2])).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        rw [hgdef]
        refine div_nonneg (mul_nonneg (le_of_lt hz.1) (by linarith [hz.2])) (by linarith [hz.2])
    intro z hz
    have hf0 : f 0 = 0 := by simp [hfdef]
    have := hmono (Set.left_mem_Icc.2 (by norm_num)) hz hz.1
    have hfz : f z = Real.log (1 - z) + z + z ^ 2 := rfl
    linarith [this, hf0.ge, hf0.le, hfz.ge, hfz.le]
  have := hle x ⟨hx0, hx⟩
  linarith

end D5.S3.Arith.Lattices.Klartag

namespace D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates

/-- Uniform logarithm bounds on the literal two-left/one-right window. -/
theorem buffer_log_size {x z : ℝ}
    (hx : 256 ≤ x) (hzl : x-2 ≤ z) (hzu : z ≤ x+1) :
    5 < Real.log z ∧ Real.log z ≤ x/20 := by
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < z := by linarith
  have he5 : Real.exp (5 : ℝ) < 243 := by
    rw [show (5 : ℝ) = (5 : ℕ)*1 by norm_num, Real.exp_nat_mul]
    have hp := pow_lt_pow_left₀ Real.exp_one_lt_three
      (Real.exp_pos _).le (by decide : (5 : ℕ) ≠ 0)
    norm_num at hp ⊢
    exact hp
  have hlow : 5 < Real.log z :=
    (Real.lt_log_iff_exp_lt hz0).mpr (by linarith)
  have hlog256 : Real.log (256 : ℝ) ≤ 8 := by
    rw [show (256 : ℝ) = 2^8 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hx1 : 0 < x+1 := by linarith
  have hs := Real.log_le_sub_one_of_pos
    (div_pos hx1 (by norm_num : (0 : ℝ) < 256))
  rw [Real.log_div hx1.ne' (by norm_num : (256 : ℝ) ≠ 0)] at hs
  have hup : Real.log (x+1) ≤ x/20 := by linarith
  exact ⟨hlow, (Real.log_le_log hz0 hzu).trans hup⟩

end D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates

namespace D5.S3.Arith.Robin.OriginalMovingWindowMoment

open Set
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)

lemma weight_continuous {a b : ℝ} (ha : 1 < a) :
    ContinuousOn weight (Icc a b) := by
  intro x hx
  have hx1 := ha.trans_le hx.1
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx1
  exact ((Real.continuousAt_log hx0.ne').add continuousAt_const).div
    ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0.ne').pow 2))
    (mul_ne_zero (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hl.ne'))
    |>.continuousWithinAt

end D5.S3.Arith.Robin.OriginalMovingWindowMoment

namespace D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

noncomputable section

def primeCutoff (z : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊z⌋₊).filter Nat.Prime

theorem prime_filter_Icc (t : ℝ) :
    (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime = primeCutoff t := by
  ext n
  simp only [primeCutoff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hn⟩, hp⟩
    exact ⟨⟨hp.pos, hn⟩, hp⟩
  · rintro ⟨⟨_, hn⟩, hp⟩
    exact ⟨⟨Nat.zero_le n, hn⟩, hp⟩

end
end D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
