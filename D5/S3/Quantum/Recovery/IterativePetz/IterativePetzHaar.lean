/- GID: D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove a strict limiting Haar fidelity deficit for iterative Petz recovery. -/

import D5.S3.Quantum.Recovery.IterativePetz.IterativePetzDephasing
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Quantum.Recovery.IterativePetz.IterativePetzHaar

open IterativePetzDephasing

private def targetCoherence (z : ℝ) : ℝ := Real.sqrt (1 - z ^ 2) / 2

private def orbit (a z : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a ^ 2 * targetCoherence z, z)
  | n + 1 => step a (orbit a z n).1 (orbit a z n).2

private def fidelity (a : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  blochFidelity (targetCoherence z) z (orbit a z n).1 (orbit a z n).2

private theorem target_data {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    0 < targetCoherence z ∧ 4 * targetCoherence z ^ 2 + z ^ 2 = 1 := by
  have hlo : 0 < 1 + z := by linarith [hz.1]
  have hhi : 0 < 1 - z := by linarith [hz.2]
  have h : 0 < 1 - z ^ 2 := by nlinarith only [mul_pos hlo hhi]
  unfold targetCoherence
  exact ⟨by positivity, by nlinarith [Real.sq_sqrt h.le]⟩

private theorem orbit_interior {a z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (n : ℕ) :
    0 < (orbit a z n).1 ∧ 0 < blochDet (orbit a z n).1 (orbit a z n).2 := by
  induction n with
  | zero =>
    exact ⟨by change 0 < a ^ 2 * targetCoherence z
              exact mul_pos (sq_pos_of_pos ha0) (target_data hz).1,
      first_det_pos ha0 ha1 (target_data hz).1 (target_data hz).2⟩
  | succ n ih =>
    exact step_preserves_open_disk ha0 ha1 ih.1 ih.2

private theorem measurable_orbit (a : ℝ) (n : ℕ) : Measurable (fun z => orbit a z n) := by
  induction n with
  | zero =>
    change Measurable (fun z : ℝ => (a ^ 2 * targetCoherence z, z))
    unfold targetCoherence
    fun_prop
  | succ n ih =>
    change Measurable (fun z : ℝ => step a (orbit a z n).1 (orbit a z n).2)
    unfold step petzStep petzDelta petzShrink petzL blochDet
    fun_prop

private theorem measurable_fidelity (a : ℝ) (n : ℕ) : Measurable (fidelity a n) := by
  have hm := measurable_orbit a n
  unfold fidelity targetCoherence blochFidelity
  fun_prop

private theorem fidelity_mem_unit {a z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (n : ℕ) : fidelity a n z ∈ Icc 0 1 := by
  have ht := (target_data hz).2
  have hd := (orbit_interior ha0 ha1 hz n).2
  unfold blochDet at hd
  unfold fidelity blochFidelity
  constructor
  · nlinarith only [ht, hd, sq_nonneg (2 * targetCoherence z + 2 * (orbit a z n).1),
      sq_nonneg (z + (orbit a z n).2)]
  · nlinarith only [ht, hd, sq_nonneg (2 * targetCoherence z - 2 * (orbit a z n).1),
      sq_nonneg (z - (orbit a z n).2)]

private theorem fidelity_limit {a z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ∃ F ∈ Icc (0 : ℝ) 1, Tendsto (fun n => fidelity a n z) atTop (𝓝 F) ∧
      (z ≠ 0 → F < 1) := by
  obtain ⟨C, Z, hc, hz', -, hstrict, -⟩ :=
    pure_target_limit (c := fun n => (orbit a z n).1)
      (z := fun n => (orbit a z n).2) ha0 ha1 (target_data hz).1 (target_data hz).2
      rfl rfl (fun _ => rfl)
  let F := blochFidelity (targetCoherence z) z C Z
  have hF : Tendsto (fun n => fidelity a n z) atTop (𝓝 F) := by
    unfold fidelity F blochFidelity
    exact ((tendsto_const_nhds.add (hc.const_mul (4 * targetCoherence z))).add
      (hz'.const_mul z)).div_const 2
  refine ⟨F, ⟨ge_of_tendsto' hF (fun n => (fidelity_mem_unit ha0 ha1 hz n).1),
    le_of_tendsto' hF (fun n => (fidelity_mem_unit ha0 ha1 hz n).2)⟩, hF, ?_⟩
  intro hn
  obtain ⟨hg, -, h⟩ := hstrict hn
  exact h.trans_lt (by nlinarith only [sq_pos_of_pos hg])

/-- The normalized axial uniform integral equals the Haar average of any
phase-invariant qubit fidelity. The open interval has full Haar measure. -/
def meanFidelity (a : ℝ) (n : ℕ) : ℝ :=
  (∫ z in Ioo (-1 : ℝ) 1, fidelity a n z) / 2

/-- The Haar mean for the ideal single-axis protocol converges strictly below one. -/
theorem meanFidelity_tendsto_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ L < 1, Tendsto (meanFidelity a) atTop (𝓝 L) := by
  let I := Ioo (-1 : ℝ) 1
  let μ : Measure ℝ := volume.restrict I
  have hmass : μ univ = 2 := by
    rw [show μ univ = volume I from Measure.restrict_apply_univ I]
    norm_num [I, Real.volume_Ioo]
  let : IsFiniteMeasure μ := ⟨by rw [hmass]; norm_num⟩
  have hpoint (z : ℝ) : ∃ F ∈ Icc (0 : ℝ) 1, z ∈ I →
      Tendsto (fun n => fidelity a n z) atTop (𝓝 F) ∧ (z ≠ 0 → F < 1) := by
    by_cases hz : z ∈ I
    · obtain ⟨F, hF, hlim, hstrict⟩ := fidelity_limit ha0 ha1 hz
      exact ⟨F, hF, fun _ => ⟨hlim, hstrict⟩⟩
    · exact ⟨0, by norm_num, fun h => (hz h).elim⟩
  choose F hF hlim using hpoint
  have hmem : ∀ᵐ z ∂μ, z ∈ I := ae_restrict_mem measurableSet_Ioo
  have hlim_ae : ∀ᵐ z ∂μ, Tendsto (fun n => fidelity a n z) atTop (𝓝 (F z)) :=
    hmem.mono (fun z hz => (hlim z hz).1)
  have hFmeas : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (measurable_fidelity a n).aestronglyMeasurable) hlim_ae
  have hFint : Integrable F μ := Integrable.of_bound hFmeas 1
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs, abs_of_nonneg (hF z).1] using (hF z).2)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (measurable_fidelity a n).aestronglyMeasurable) hone
    (fun n => hmem.mono fun z hz => by
      have hf := fidelity_mem_unit ha0 ha1 hz n
      simpa [Real.norm_eq_abs, abs_of_nonneg hf.1] using hf.2) hlim_ae
  have hgap : 0 < ∫ z, (1 - F z) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun z => sub_nonneg.mpr (hF z).2)
      (hone.sub hFint)).2
    have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (fun z => 1 - F z) := by
      intro z hz
      have hi : z ∈ I := ⟨by linarith [hz.1], hz.2⟩
      exact (sub_pos.mpr ((hlim z hi).2 (ne_of_gt hz.1))).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [show μ (Ioo (0 : ℝ) 1) = volume (Ioo (0 : ℝ) 1) by
      rw [Measure.restrict_apply measurableSet_Ioo]
      congr 1
      exact inter_eq_left.mpr (fun z hz => ⟨by linarith [hz.1], hz.2⟩)]
    simp [Real.volume_Ioo]
  have hconst : (∫ _ : ℝ, (1 : ℝ) ∂μ) = 2 := by
    simp [MeasureTheory.integral_const, Measure.real, hmass]
  rw [integral_sub hone hFint, hconst] at hgap
  exact ⟨(∫ z, F z ∂μ) / 2, by linarith, hDCT.div_const 2⟩

#print axioms meanFidelity_tendsto_lt_one

end D5.S3.Quantum.Recovery.IterativePetz.IterativePetzHaar
