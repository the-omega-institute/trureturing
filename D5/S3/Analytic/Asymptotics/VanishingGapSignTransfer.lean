/- GID: D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/VanishingGapSignTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vanishing forward gaps transfer fixed excursions to arbitrarily late samples. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Fixed-size excursions on meshes with vanishing gaps

A first crossing can be taken after any prescribed index. Uniform continuity
then transfers any fixed-size excursion to a sample with vanishing error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer

/-- Every sufficiently late interval of width `ε` has a sample at or after
`K`. The first crossing uses only an upper bound on the forward increments. -/
private theorem first_crossing_after {y : ℕ → ℝ} (hy : Tendsto y atTop atTop)
    {ε : ℝ} (K : ℕ)
    (hgap : ∀ k : ℕ, K ≤ k → y (k + 1) - y k < ε) :
    ∀ t : ℝ, y K < t → ∃ k : ℕ, K ≤ k ∧ t ≤ y k ∧ y k < t + ε := by
  classical
  intro t ht
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hy.eventually (eventually_ge_atTop t))
  have hex : ∃ n : ℕ, t ≤ y (K + n) := ⟨L, hL (K + L) (by omega)⟩
  have hpos : 0 < Nat.find hex := by
    apply (Nat.find_pos hex).mpr
    simpa only [Nat.add_zero] using (not_le_of_gt ht)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.find hex = j + 1 :=
    ⟨Nat.find hex - 1, by omega⟩
  have hprev : y (K + j) < t :=
    lt_of_not_ge (Nat.find_min hex (show j < Nat.find hex by omega))
  have hstep := hgap (K + j) (by omega)
  have hcross := Nat.find_spec hex
  rw [hj, ← Nat.add_assoc] at hcross
  exact ⟨K + j + 1, by omega, hcross, by linarith only [hprev, hstep]⟩

/-- The eventual interval-hitting statement for a vanishing-gap mesh. -/
theorem eventually_hit_interval {y : ℕ → ℝ} (hy : Tendsto y atTop atTop)
    (hgap : Tendsto (fun k => y (k + 1) - y k) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ k : ℕ, K ≤ k ∧ t ≤ y k ∧ y k < t + ε := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hgap.eventually (gt_mem_nhds hε))
  let L := max K K₀
  refine ⟨y L + 1, ?_⟩
  intro t ht
  obtain ⟨k, hk, hlo, hhi⟩ := first_crossing_after hy L
    (fun k hk => hK₀ k ((le_max_right K K₀).trans hk)) t (by linarith only [ht])
  exact ⟨k, (le_max_left K K₀).trans hk, hlo, hhi⟩

/-- When the samples approximate `-F`, a fixed positive excursion of `F`
gives a fixed negative excursion on the mesh. -/
theorem arbitrarily_late_negative_samples {F : ℝ → ℝ} {y a : ℕ → ℝ}
    (hF : UniformContinuous F) (hy : Tendsto y atTop atTop)
    (hgap : Tendsto (fun k => y (k + 1) - y k) atTop (𝓝 0))
    (happrox : Tendsto (fun k => a k + F (y k)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hpeak : ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ 3 * c ≤ F t) :
    ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ a k < -c := by
  intro K
  obtain ⟨ε, hε, hmod⟩ := Metric.uniformContinuous_iff.mp hF c hc
  obtain ⟨L, hL⟩ := eventually_atTop.mp (happrox.eventually (gt_mem_nhds hc))
  obtain ⟨T, hT⟩ := eventually_hit_interval hy hgap hε (max K L)
  obtain ⟨t, ht, htpeak⟩ := hpeak T
  obtain ⟨k, hk, hlo, hhi⟩ := hT t ht
  have hnear : dist (y k) t < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith only [hhi]
  have hdiff := hmod (a := y k) (b := t) hnear
  rw [Real.dist_eq] at hdiff
  have hleft := (abs_lt.mp hdiff).1
  have herr : a k + F (y k) < c := hL k ((le_max_right K L).trans hk)
  exact ⟨k, (le_max_left K L).trans hk, by linarith only [htpeak, hleft, herr]⟩

/-- For a positive sequence tending to infinity, a successive ratio tending
to one supplies the log-coordinate hypotheses for sign transfer. -/
theorem log_mesh_of_ratio_one {x : ℕ → ℝ} (hx : Tendsto x atTop atTop)
    (hratio : Tendsto (fun k => x (k + 1) / x k) atTop (𝓝 1)) :
    Tendsto (fun k => Real.log (x k)) atTop atTop ∧
    Tendsto (fun k => Real.log (x (k + 1)) - Real.log (x k)) atTop (𝓝 0) := by
  refine ⟨Real.tendsto_log_atTop.comp hx, ?_⟩
  have hlog : Tendsto (fun k => Real.log (x (k + 1) / x k)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hx₀ := hx.eventually (eventually_gt_atTop (0 : ℝ))
  have hsucc : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ k) tendsto_id
  apply hlog.congr'
  filter_upwards [hx₀, hsucc.eventually hx₀] with k hk hk₁
  exact Real.log_div (ne_of_gt hk₁) (ne_of_gt hk)

end D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer
