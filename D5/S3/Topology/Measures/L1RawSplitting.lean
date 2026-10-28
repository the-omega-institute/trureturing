/- GID: D5/S3/Topology/Measures/L1RawSplitting
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1RawSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real L1 splitting into disjoint raw restrictions and a weak remainder. -/

import D5.S3.Topology.Measures.L1Biting
import D5.S3.Topology.Measures.L1Disjointization
import D5.S3.Topology.Measures.L1UniformIntegrableWeak

/-! Classical subsequence splitting with actual disjoint measurable carriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology

namespace D5.S3.Topology.Measures.L1RawSplitting

open L1Restriction

universe u
variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Classical real L1 subsequence splitting on arbitrary finite measures.
Both summands are literal restrictions, the carriers are disjoint as sets,
and weak convergence tests every continuous real linear functional.
This supplier does not resolve the full signed CH/Talagrand endpoint. -/
theorem exists_raw_restriction_splitting (f : ℕ → Lp ℝ 1 μ)
    (hb : ∃ B : ℝ, ∀ n, ‖f n‖ ≤ B) :
    ∃ (j : ℕ → ℕ) (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
      (v : Lp ℝ 1 μ) (r : ℝ),
      StrictMono j ∧ Pairwise (fun i n => Disjoint (E i) (E n)) ∧
      (∀ n, f (j n) = restrict (E n) (hE n) (f (j n)) +
        restrict (E n)ᶜ (hE n).compl (f (j n))) ∧
      (∀ n, ‖restrict (E n) (hE n) (f (j n))‖ +
        ‖restrict (E n)ᶜ (hE n).compl (f (j n))‖ = ‖f (j n)‖) ∧
      (∀ φ : Lp ℝ 1 μ →L[ℝ] ℝ,
        Tendsto (fun n => φ (restrict (E n)ᶜ (hE n).compl (f (j n)))) atTop (𝓝 (φ v))) ∧
      0 ≤ r ∧ Tendsto (fun n => ‖restrict (E n) (hE n) (f (j n))‖) atTop (𝓝 r) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨j, K, c, α, hj, hK, hα, hαk, hc, hfixed, hmoving, hcross⟩ :=
    L1TailConcentration.exists_tail_concentration f B hB
  let F (n : ℕ) := f (j n)
  let A (n : ℕ) := tailSet (K n) (F n)
  have hA (n : ℕ) : MeasurableSet (A n) := measurable_tailSet _ _
  let g (n : ℕ) := restrict (A n)ᶜ (hA n).compl (F n)
  have hgui : UniformIntegrable (fun n => (g n : Ω → ℝ)) 1 μ :=
    L1Biting.uniformIntegrable_complements F K B α c (fun n => hB (j n)) hK hc hfixed hmoving
  obtain ⟨E, hE, hdisj, hmass, herr⟩ :=
    L1Disjointization.exists_disjoint_restrictions F A hA α hcross hmoving
  let w (n : ℕ) := restrict (E n)ᶜ (hE n).compl (F n)
  have herror : Tendsto (fun n => w n - g n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 herr
  obtain ⟨a, v, ha, hweak⟩ := L1UniformIntegrableWeak.exists_weak_subsequence μ g hgui
  refine ⟨j ∘ a, E ∘ a, fun n => hE (a n), v, α, hj.comp ha,
    fun i n hin => hdisj (ha.injective.ne hin), fun n => (add_compl _ _ _).symm,
    fun n => norm_add_compl _ _ _, ?_, hα, hmass.comp ha.tendsto_atTop⟩
  intro φ
  have hsmall := φ.continuous.continuousAt.tendsto.comp (herror.comp ha.tendsto_atTop)
  have heq (n : ℕ) : φ (g (a n)) + φ (w (a n) - g (a n)) = φ (w (a n)) := by
    rw [map_sub, ← add_sub_assoc, add_sub_cancel_left]
  simpa only [Function.comp_apply, heq, map_zero, add_zero] using (hweak φ).add hsmall

end D5.S3.Topology.Measures.L1RawSplitting
