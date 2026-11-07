/- GID: D5/S3/Quantum/Analysis/NonautonomousEvolutionStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NonautonomousEvolutionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong L1 coefficient convergence along compact families of vector paths. -/

import D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

/-! # Strong L1 stability of nonautonomous evolution -/

open scoped Nat Topology
open MeasureTheory Filter
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.NonautonomousEvolutionStability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem evaluation_integrable_of_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (D : α → E →L[ℂ] E)
    (hD : ∀ x, AEStronglyMeasurable (fun s => D s x) μ)
    {c : α → ℝ} (hc : Integrable c μ) (hcn : 0 ≤ᵐ[μ] c)
    (hDc : ∀ᵐ s ∂μ, ‖D s‖ ≤ c s)
    {v : α → E} (hv : AEStronglyMeasurable v μ)
    (C : ℝ) (hvC : ∀ᵐ s ∂μ, ‖v s‖ ≤ C) :
    Integrable (fun s => D s (v s)) μ := by
  apply (hc.mul_const C).mono' (aestronglyMeasurable_evaluation D hD hv)
  filter_upwards [hcn, hDc, hvC] with s hcs hDs hvs
  exact ((D s).le_opNorm _).trans (mul_le_mul hDs hvs (norm_nonneg _) hcs)

/-- Fixed-vector L1 convergence controls all measurable paths in a compact vector range,
uniformly over the paths. Each evaluated vector function is actually Bochner integrable. -/
theorem uniform_integral_evaluation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (D : ℕ → α → E →L[ℂ] E)
    (hD : ∀ n x, AEStronglyMeasurable (fun s => D n s x) μ)
    {c : α → ℝ} (hc : Integrable c μ) (hcn : 0 ≤ᵐ[μ] c)
    (hDc : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ c s)
    (hlim : ∀ x, Tendsto (fun n => ∫ s, ‖D n s x‖ ∂μ) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K) :
    (∀ n (v : α → E), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → Integrable (fun s => D n s (v s)) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      (∫ s, ‖D n s (v s)‖ ∂μ) < ε := by
  classical
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x : E => x) continuousOn_id
  have hi : ∀ n (v : α → E), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → Integrable (fun s => D n s (v s)) μ := by
    intro n v hv hvK
    exact evaluation_integrable_of_bound (D n) (hD n) hc hcn (hDc n) hv C
      (hvK.mono fun s hs => hC _ hs)
  refine ⟨hi, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt (half_pos hε) (∫ s, c s ∂μ)
  obtain ⟨A, hAK, hAf, hcover⟩ := hK.finite_cover_balls hδ
  let F := hAf.toFinset
  have hfixed : ∀ n x, Integrable (fun s => D n s x) μ := by
    intro n x
    exact evaluation_integrable_of_bound (D n) (hD n) hc hcn (hDc n)
      aestronglyMeasurable_const ‖x‖ (Eventually.of_forall fun _ => le_rfl)
  have hsumlim : Tendsto (fun n => ∑ x ∈ F, ∫ s, ‖D n s x‖ ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum F (fun x _ => hlim x)
  filter_upwards [hsumlim.eventually (gt_mem_nhds (half_pos hε))] with n hn
  intro v hv hvK
  have hsum : Integrable (fun s => ∑ x ∈ F, ‖D n s x‖) μ :=
    integrable_finsetSum F (fun x _ => (hfixed n x).norm)
  have hpoint : ∀ᵐ s ∂μ,
      ‖D n s (v s)‖ ≤ (∑ x ∈ F, ‖D n s x‖) + c s * δ := by
    filter_upwards [hvK, hcn, hDc n] with s hvs hcs hDs
    obtain ⟨x, hxA, hx⟩ := Set.mem_iUnion₂.mp (hcover hvs)
    have hxF : x ∈ F := hAf.mem_toFinset.mpr hxA
    have hdist : ‖v s - x‖ ≤ δ := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le
    calc
      ‖D n s (v s)‖ = ‖D n s (v s - x) + D n s x‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖D n s (v s - x)‖ + ‖D n s x‖ := norm_add_le _ _
      _ ≤ c s * δ + ‖D n s x‖ := by
        gcongr
        exact ((D n s).le_opNorm _).trans
          (mul_le_mul hDs hdist (norm_nonneg _) hcs)
      _ ≤ (∑ x ∈ F, ‖D n s x‖) + c s * δ := by
        have hxsum := Finset.single_le_sum (fun y (_ : y ∈ F) => norm_nonneg (D n s y)) hxF
        linarith
  calc
    (∫ s, ‖D n s (v s)‖ ∂μ) ≤
        ∫ s, (∑ x ∈ F, ‖D n s x‖) + c s * δ ∂μ :=
      integral_mono_ae (hi n v hv hvK).norm (hsum.add (hc.mul_const δ)) hpoint
    _ = (∑ x ∈ F, ∫ s, ‖D n s x‖ ∂μ) + (∫ s, c s ∂μ) * δ := by
      rw [integral_add hsum (hc.mul_const δ), integral_finsetSum F
        (fun x _ => (hfixed n x).norm), integral_mul_const]
    _ < ε := by linarith

end D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
