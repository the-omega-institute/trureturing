/- GID: D5/S3/Topology/Measures/L1Biting
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1Biting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous hard-tail limits give uniformly integrable literal complements. -/

import D5.S3.Topology.Measures.L1TailConcentration

/-! Uniform integrability of the literal complements of concentration tails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.L1Biting

open L1Restriction L1TailConcentration

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem eLpNorm_tail (f : Lp ℝ 1 μ) (k : ℕ) :
    eLpNorm ({x | (k : ℝ≥0) ≤ ‖f x‖₊}.indicator f) 1 μ = ENNReal.ofReal (tailNorm k f) := by
  have heq : {x | (k : ℝ≥0) ≤ ‖f x‖₊} = tailSet k f := by
    ext x
    exact_mod_cast (show ((k : ℝ≥0) ≤ ‖f x‖₊) ↔ (k : ℝ) ≤ ‖f x‖ from NNReal.coe_le_coe.symm)
  rw [heq, tailNorm, ofReal_norm, Lp.enorm_def,
    eLpNorm_congr_ae (coe_restrict _ (measurable_tailSet k f) f)]

private theorem uniformIntegrable_of_eventual_tailNorm
    (f : ℕ → Lp ℝ 1 μ) (B : ℝ) (hb : ∀ n, ‖f n‖ ≤ B)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ k N : ℕ, ∀ n, N ≤ n → tailNorm k (f n) ≤ ε) :
    UniformIntegrable (fun n => (f n : Ω → ℝ)) 1 μ := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) (fun n => Lp.aestronglyMeasurable (f n))
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨0, fun n => by simp [htop]⟩
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨k, N, hlate⟩ := htail ε.toReal hεpos
  have ev := eventually_small_cross_tails f B hb N ε.toReal hεpos
  obtain ⟨K, hkK, hfinite⟩ : ∃ K, k ≤ K ∧ ∀ n, n ≤ N → tailNorm K (f n) ≤ ε.toReal := by
    have ev' : ∀ᶠ K in atTop, k ≤ K ∧ ∀ n, n ≤ N → tailNorm K (f n) ≤ ε.toReal := by
      filter_upwards [eventually_ge_atTop k, ev] with K hk hK
      exact ⟨hk, fun n hn => hK n hn n⟩
    exact ev'.exists
  refine ⟨K, fun n => ?_⟩
  rw [eLpNorm_tail]
  have hnorm : tailNorm K (f n) ≤ ε.toReal := by
    by_cases hn : n ≤ N
    · exact hfinite n hn
    · exact (tailNorm_antitone (f n) hkK).trans (hlate n (by omega))
  exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq (ENNReal.ofReal_toReal htop)

/-- Convergence of all fixed hard tails and of the selected moving tail makes
the literal low restrictions uniformly integrable. Finite initial families and
the strict positivity of the test threshold are retained. -/
theorem uniformIntegrable_complements
    (f : ℕ → Lp ℝ 1 μ) (K : ℕ → ℕ) (B α : ℝ) (c : ℕ → ℝ)
    (hb : ∀ n, ‖f n‖ ≤ B) (hK : ∀ n, n < K n)
    (hc : Tendsto c atTop (𝓝 α))
    (hfixed : ∀ k, Tendsto (fun n => tailNorm k (f n)) atTop (𝓝 (c k)))
    (hmoving : Tendsto (fun n => tailNorm (K n) (f n)) atTop (𝓝 α)) :
    UniformIntegrable (fun n =>
      (restrict (tailSet (K n) (f n))ᶜ (measurable_tailSet (K n) (f n)).compl (f n) : Ω → ℝ)) 1 μ := by
  let g (n : ℕ) := restrict (tailSet (K n) (f n))ᶜ (measurable_tailSet (K n) (f n)).compl (f n)
  apply uniformIntegrable_of_eventual_tailNorm g B (fun n => (norm_le _ _ _).trans (hb n))
  intro ε hε
  have hcsmall : ∀ᶠ k in atTop, c k - α < ε / 2 := by
    have hz : Tendsto (fun k => c k - α) atTop (𝓝 0) := by
      simpa using hc.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => α) atTop (𝓝 α))
    exact (tendsto_order.1 hz).2 (ε / 2) (by linarith)
  obtain ⟨k, hk, hck⟩ : ∃ k : ℕ, 0 < k ∧ c k - α < ε / 2 :=
    ((eventually_gt_atTop 0).and hcsmall).exists
  have heq : (fun n => tailNorm k (g n)) =ᶠ[atTop]
      (fun n => tailNorm k (f n) - tailNorm (K n) (f n)) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact tailNorm_compl (f n) k (K n) hk (hn.trans (hK n).le)
  have ht : Tendsto (fun n => tailNorm k (g n)) atTop (𝓝 (c k - α)) :=
    ((hfixed k).sub hmoving).congr' heq.symm
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 ε (by linarith))
  exact ⟨k, N, fun n hn => (hN n hn).le⟩

end D5.S3.Topology.Measures.L1Biting
