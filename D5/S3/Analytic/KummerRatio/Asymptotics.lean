/- GID: D5/S3/Analytic/KummerRatio/Asymptotics
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Asymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics]
   utility: none
   digest: Gamma-normalized endpoint asymptotics of the entire Kummer series. -/

import D5.S3.Analytic.KummerRatio.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology
open D5.S3.Analytic.KummerRatio.Defs
open D5.S3.Analytic.KummerRatio.Series

namespace D5.S3.Analytic.KummerRatio.Asymptotics

private lemma scaled_contiguous {s c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.exp (-x) * x ^ (c - s) * kummer s c x =
      x⁻¹ * (Real.exp (-x) * x ^ ((c + 1) - s) * kummer s (c + 1) x) +
      s / (c * (c + 1)) *
        (Real.exp (-x) * x ^ ((c + 2) - (s + 1)) * kummer (s + 1) (c + 2) x) := by
  have hp : x ^ (c + 1 - s) = x ^ (c - s) * x := by
    rw [show c + 1 - s = (c - s) + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  rw [show c + 2 - (s + 1) = c + 1 - s by ring, hp, kummer_contiguous s hc]
  field_simp [hx.ne']
  <;> ring

private lemma gamma_step_constant {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    s / (c * (c + 1)) * (Real.Gamma (c + 2) / Real.Gamma (s + 1)) =
      Real.Gamma c / Real.Gamma s := by
  rw [show c + 2 = (c + 1) + 1 by ring,
    Real.Gamma_add_one (by positivity : c + 1 ≠ 0),
    Real.Gamma_add_one hc.ne', Real.Gamma_add_one hs.ne']
  have hg := (Real.Gamma_pos_of_pos hs).ne'
  have hc1 : c + 1 ≠ 0 := by positivity
  field_simp [hs.ne', hc.ne', hc1, hg]

private lemma tendsto_kummer_step {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (h₁ : Tendsto (fun x : ℝ =>
      Real.exp (-x) * x ^ ((c + 1) - s) * kummer s (c + 1) x)
      atTop (𝓝 (Real.Gamma (c + 1) / Real.Gamma s)))
    (h₂ : Tendsto (fun x : ℝ =>
      Real.exp (-x) * x ^ ((c + 2) - (s + 1)) * kummer (s + 1) (c + 2) x)
      atTop (𝓝 (Real.Gamma (c + 2) / Real.Gamma (s + 1)))) :
    Tendsto (fun x : ℝ => Real.exp (-x) * x ^ (c - s) * kummer s c x)
      atTop (𝓝 (Real.Gamma c / Real.Gamma s)) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht := (hi.mul h₁).add (h₂.const_mul (s / (c * (c + 1))))
  simp only [zero_mul, zero_add, gamma_step_constant hs hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (scaled_contiguous hc hx).symm

private lemma tendsto_kummer_of_subcritical
    (hbase : ∀ {s c : ℝ}, 0 < s → 0 < c → s < c →
      Tendsto (fun x : ℝ => Real.exp (-x) * x ^ (c - s) * kummer s c x)
        atTop (𝓝 (Real.Gamma c / Real.Gamma s)))
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-x) * x ^ (c - s) * kummer s c x)
      atTop (𝓝 (Real.Gamma c / Real.Gamma s)) := by
  have hind : ∀ n : ℕ, ∀ {s c : ℝ}, 0 < s → 0 < c → s < c + n →
      Tendsto (fun x : ℝ => Real.exp (-x) * x ^ (c - s) * kummer s c x)
        atTop (𝓝 (Real.Gamma c / Real.Gamma s)) := by
    intro n
    induction n with
    | zero =>
      intro s c hs hc hsc
      exact hbase hs hc (by simpa using hsc)
    | succ n ih =>
      intro s c hs hc hsc
      apply tendsto_kummer_step hs hc
      · apply ih hs (by linarith : 0 < c + 1)
        have hsc' : s < c + ((n : ℝ) + 1) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hsc
        linarith
      · apply ih (by linarith : 0 < s + 1) (by linarith : 0 < c + 2)
        have hsc' : s < c + ((n : ℝ) + 1) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hsc
        linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (s - c)
  apply hind n hs hc
  linarith

end D5.S3.Analytic.KummerRatio.Asymptotics
