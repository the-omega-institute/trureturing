/- GID: D5/S3/Quantum/Analysis/VaryingBackgroundEvolutionStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/VaryingBackgroundEvolutionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform strong stability under varying contraction backgrounds. -/

import D5.S3.Quantum.Analysis.SeparateMassEvolutionStability
import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform stability for varying contraction backgrounds -/

open scoped Nat Topology
open MeasureTheory Filter
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
open D5.S3.Quantum.Analysis.SeparateMassEvolutionStability

namespace D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private noncomputable def actionDifference (S₁ S : Contraction E) (T : ℝ) :
    E →L[ℂ] C(Set.Icc (0 : ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ⟨fun h => S₁.action h x - S.action h x,
          (S₁.action_continuous.comp (continuous_subtype_val.prodMk continuous_const)).sub
            (S.action_continuous.comp (continuous_subtype_val.prodMk continuous_const))⟩
      map_add' := by
        intro x y
        ext h
        change S₁.action h (x + y) - S.action h (x + y) =
          (S₁.action h x - S.action h x) + (S₁.action h y - S.action h y)
        simp only [map_add]
        abel
      map_smul' := by
        intro c x
        ext h
        change S₁.action h (c • x) - S.action h (c • x) =
          c • (S₁.action h x - S.action h x)
        simp only [map_smul, smul_sub] }
    2 (fun x => (ContinuousMap.norm_le _ (by positivity)).mpr fun h =>
      (norm_sub_le _ _).trans ((add_le_add (S₁.action_bound h x)
        (S.action_bound h x)).trans_eq (two_mul ‖x‖).symm))

private theorem actionDifference_bound (S₁ S : Contraction E) (T : ℝ) (x : E) :
    ‖actionDifference S₁ S T x‖ ≤ 2 * ‖x‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro h
  change ‖S₁.action h x - S.action h x‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add (S₁.action_bound h x)
    (S.action_bound h x)).trans_eq (two_mul ‖x‖).symm)

/-- Compact-time strong convergence of contraction backgrounds remains uniformly L1-small
after a vectorwise measurable integrably bounded coefficient, for every measurable vector
path in a fixed compact set and every measurable choice of a time in the compact interval. -/
theorem uniform_integral_background_action {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (Sseq : ℕ → Contraction E) (S : Contraction E) (T : ℝ)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (B : α → E →L[ℂ] E)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) μ)
    (g : α → ℝ) (hg : Integrable g μ) (hgn : 0 ≤ᵐ[μ] g)
    (hBg : ∀ᵐ s ∂μ, ‖B s‖ ≤ g s) {K : Set E} (hK : IsCompact K) :
    (∀ n (v : α → E) (h : α → ℝ), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → AEStronglyMeasurable h μ →
      Integrable (fun s => (Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E) (h : α → ℝ),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      AEStronglyMeasurable h μ → (∀ᵐ s ∂μ, h s ∈ Set.Icc 0 T) →
      (∫ s, ‖(Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))‖ ∂μ) < ε := by
  classical
  let F := C(Set.Icc (0 : ℝ) T, E)
  let U : ℕ → E →L[ℂ] F := fun n => actionDifference (Sseq n) S T
  have hU : ∀ x, Tendsto (fun n => U n x) atTop (𝓝 0) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := hSlim x ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [dist_zero_right]
    apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro h
    exact hN n hn h h.2.1 h.2.2
  have hfixed_meas : ∀ n x, AEStronglyMeasurable (fun s => U n (B s x)) μ := by
    intro n x
    exact (U n).continuous.comp_aestronglyMeasurable (hB x)
  have hfixed_bound : ∀ n x, ∀ᵐ s ∂μ,
      ‖U n (B s x)‖ ≤ (g s * 2) * ‖x‖ := by
    intro n x
    filter_upwards [hBg] with s hs
    exact (actionDifference_bound (Sseq n) S T _).trans (by
      have hb := ((B s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x))
      nlinarith)
  have hfixed : ∀ x, Tendsto (fun n => ∫ s, ‖U n (B s x)‖ ∂μ) atTop (𝓝 0) := by
    intro x
    have hd := tendsto_integral_of_dominated_convergence
      (fun s => (g s * 2) * ‖x‖) (fun n => (hfixed_meas n x).norm)
      ((hg.mul_const 2).mul_const ‖x‖)
      (fun n => by simpa only [Real.norm_eq_abs, abs_norm] using hfixed_bound n x)
      (Eventually.of_forall fun s => (hU (B s x)).norm)
    simpa only [norm_zero, integral_zero] using hd
  let D : ℕ → α → (E × F) →L[ℂ] (E × F) := fun n s =>
    (0 : (E × F) →L[ℂ] E).prod
      (((U n).comp (B s)).comp (ContinuousLinearMap.fst ℂ E F))
  have hDnorm : ∀ n s z, ‖D n s z‖ = ‖U n (B s z.1)‖ := by
    intro n s z
    change max ‖(0 : E)‖ ‖U n (B s z.1)‖ = _
    rw [norm_zero, max_eq_right (norm_nonneg _)]
  have hD : ∀ n z, AEStronglyMeasurable (fun s => D n s z) μ := by
    intro n z
    exact aestronglyMeasurable_const.prodMk (hfixed_meas n z.1)
  have hDb : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ g s * 2 := by
    intro n
    filter_upwards [hBg, hgn] with s hs hgs
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hgs (by positivity))
    intro z
    change ‖((0 : E), U n (B s z.1))‖ ≤ _
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact (actionDifference_bound (Sseq n) S T _).trans (by
      have hb := ((B s).le_opNorm z.1).trans
        (mul_le_mul hs (norm_fst_le z) (norm_nonneg _) hgs)
      nlinarith)
  have hDlim : ∀ z, Tendsto (fun n => ∫ s, ‖D n s z‖ ∂μ) atTop (𝓝 0) := by
    intro z
    simp_rw [hDnorm]
    exact hfixed z.1
  have hK' : IsCompact ((fun x : E => (x, (0 : F))) '' K) :=
    hK.image (continuous_id.prodMk continuous_const)
  have hu := uniform_integral_evaluation_of_mass D hD (fun _ => hg.mul_const 2)
    (fun _ => hgn.mono fun s hs => mul_nonneg hs (by positivity)) hDb
    (∫ s, g s * 2 ∂μ) (fun _ => le_rfl) hDlim hK'
  have hi : ∀ n (v : α → E) (h : α → ℝ), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → AEStronglyMeasurable h μ →
      Integrable (fun s => (Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))) μ := by
    intro n v h hv hvK hh
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x : E => x) continuousOn_id
    have hiv := evaluation_integrable_of_bound B hB hg hgn hBg hv C
      (hvK.mono fun s hs => hC _ hs)
    apply (hiv.norm.mul_const 2).mono'
      (((Sseq n).action_continuous.comp_aestronglyMeasurable
        (hh.prodMk hiv.aestronglyMeasurable)).sub
        (S.action_continuous.comp_aestronglyMeasurable (hh.prodMk hiv.aestronglyMeasurable)))
    exact Eventually.of_forall fun s => (norm_sub_le _ _).trans (by
      linarith [(Sseq n).action_bound (h s) (B s (v s)),
        S.action_bound (h s) (B s (v s))])
  refine ⟨hi, ?_⟩
  intro ε hε
  filter_upwards [hu.2 ε hε] with n hn
  intro v h hv hvK hh hhT
  have hv' : AEStronglyMeasurable (fun s => (v s, (0 : F))) μ :=
    hv.prodMk aestronglyMeasurable_const
  have hvK' : ∀ᵐ s ∂μ, (v s, (0 : F)) ∈ (fun x : E => (x, (0 : F))) '' K :=
    hvK.mono fun s hs => ⟨v s, hs, rfl⟩
  have hsmall := hn (fun s => (v s, (0 : F))) hv' hvK'
  apply lt_of_le_of_lt (b := ∫ s, ‖D n s (v s, (0 : F))‖ ∂μ) _ hsmall
  apply integral_mono_ae (hi n v h hv hvK hh).norm (hu.1 n _ hv' hvK').norm
  filter_upwards [hhT] with s hs
  have hb := ContinuousMap.norm_coe_le_norm (U n (B s (v s))) ⟨h s, hs⟩
  change ‖(Sseq n).action (h s) (B s (v s)) - S.action (h s) (B s (v s))‖ ≤
    ‖U n (B s (v s))‖ at hb
  rw [hDnorm]
  exact hb

end D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
