/- GID: D5/S3/Fourier/Asymptotics/PeriodicSublevelSampling
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/PeriodicSublevelSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Low frequency bounds give a weighted small-sublevel count at regular periodic zeros. -/

import D5.S3.Fourier.Asymptotics.PlanarWindowSampling
import OmegaMath.Analysis.PeriodicSublevelSampling

/-! The small-sublevel limit for the periodic planar sampling problem. -/

namespace D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling

open Filter MeasureTheory
open scoped ContDiff Topology
open PlanarFourierTail PlanarWindowSampling
open Omega.Analysis.PeriodicSublevelSandwich (latticeVector openCell closedCell)

private theorem tendsto_window_average {α β : Type*} (l : Filter α) (g : Plane → ℝ)
    (hg : ContDiff ℝ ∞ g) (hg' : HasCompactSupport g) (center : Plane)
    (s : α → Finset β) (p : α → β → Plane) (w : α → β → ℝ)
    (hw : ∀ n, ∀ j ∈ s n, 0 ≤ w n j) (hw₁ : ∀ n, ∑ j ∈ s n, w n j = 1)
    (ε : α → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε l (𝓝 0))
    (J : α → ℕ) (hJ : ∀ n, 0 < J n) (c d : α → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 ≤ d n)
    (hmode : ∀ n m, m ≠ (0, 0) → modeRadius m ≤ J n →
      ‖∑ j ∈ s n, (w n j : ℂ) * character m (p n j)‖ ≤
        c n + d n * (modeRadius m : ℝ) ^ 2)
    (hc₀ : Tendsto (fun n => c n / (ε n) ^ 2) l (𝓝 0))
    (hd₀ : Tendsto (fun n => d n / (ε n) ^ 4) l (𝓝 0))
    (htail : Tendsto (fun n => 1 / ((ε n) ^ 6 * (J n : ℝ) ^ 4)) l (𝓝 0)) :
    Tendsto (fun n => (∑ j ∈ s n, w n j *
      ∑' a : Fin 2 → ℤ, g ((ε n)⁻¹ • (latticeVector a + p n j - center))) / (ε n) ^ 2)
      l (𝓝 (∫ u, g u)) := by
  have hdiff : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hsupp : HasCompactSupport (fun x => (g x : ℂ)) := by
    unfold HasCompactSupport tsupport at hg' ⊢
    convert hg' using 2
    ext x
    simp [Function.mem_support]
  obtain ⟨K, _, estimate⟩ := compact_window_sampling (fun x => (g x : ℂ)) hsupp hdiff
  have hb₁ := tendsto_const_nhds (x := 27 * K) |>.mul hc₀
  have hb₂ := tendsto_const_nhds (x := 27 * K) |>.mul hd₀
  have hb₃ := tendsto_const_nhds (x := 2 * K) |>.mul htail
  have hbound : Tendsto (fun n => 27 * K * (c n / (ε n) ^ 2) +
      27 * K * (d n / (ε n) ^ 4) + 2 * K * (1 / ((ε n) ^ 6 * (J n : ℝ) ^ 4)))
      l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hb₁.add hb₂).add hb₃
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [(tendsto_order.1 hε).2 1 zero_lt_one] with n he
  have hestimate := estimate (ε n) (hεpos n) he.le center (s n) (w n) (p n)
    (J n) (c n) (d n) (hc n) (hd n) (hJ n) (hw n) (hw₁ n) (hmode n)
  have hreal :
      ‖(∑ j ∈ s n, w n j *
        ∑' a : Fin 2 → ℤ, g ((ε n)⁻¹ • (latticeVector a + p n j - center))) -
          (ε n) ^ 2 * ∫ u, g u‖ ≤
      27 * K * c n + (27 * K / (ε n) ^ 2) * d n + 2 * K / ((ε n) ^ 4 * (J n : ℝ) ^ 4) := by
    simpa only [latticeVector, ← Complex.ofReal_tsum, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, integral_complex_ofReal, Complex.real_smul, ← Complex.ofReal_sub,
      Complex.norm_real] using hestimate
  have he₀ : ε n ≠ 0 := (hεpos n).ne'
  have hsquare : 0 < (ε n) ^ 2 := pow_pos (hεpos n) _
  have halgebra (x y : ℝ) :
      x / (ε n) ^ 2 - y = (x - (ε n) ^ 2 * y) / (ε n) ^ 2 := by
    field_simp [he₀]
  rw [halgebra, norm_div, Real.norm_of_nonneg hsquare.le]
  refine (div_le_div_of_nonneg_right hreal hsquare.le).trans_eq ?_
  have hJn : (J n : ℝ) ≠ 0 := by exact_mod_cast (hJ n).ne'
  field_simp [he₀, hJn]

/-- The determinant coefficient is the limit of the normalized weighted strict-sublevel mass. -/
theorem tendsto_weighted_sublevel_of_fourier {ι α β : Type*} [Fintype ι]
    (l : Filter α) (q : Plane) {F : Plane → Plane} (hF : Continuous F)
    (hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : ι → Plane) (hz : Function.Injective z)
    (hcell : ∀ i, z i ∈ openCell q)
    (hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : ι → Plane ≃L[ℝ] Plane)
    (hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    (s : α → Finset β) (p : α → β → Plane) (w : α → β → ℝ)
    (hw : ∀ n, ∀ j ∈ s n, 0 ≤ w n j) (hw₁ : ∀ n, ∑ j ∈ s n, w n j = 1)
    (ε : α → ℝ) (hεpos : ∀ n, 0 < ε n) (hε : Tendsto ε l (𝓝 0))
    (J : α → ℕ) (hJ : ∀ n, 0 < J n) (c d : α → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 ≤ d n)
    (hmode : ∀ n m, m ≠ (0, 0) → modeRadius m ≤ J n →
      ‖∑ j ∈ s n, (w n j : ℂ) * character m (p n j)‖ ≤
        c n + d n * (modeRadius m : ℝ) ^ 2)
    (hc₀ : Tendsto (fun n => c n / (ε n) ^ 2) l (𝓝 0))
    (hd₀ : Tendsto (fun n => d n / (ε n) ^ 4) l (𝓝 0))
    (htail : Tendsto (fun n => 1 / ((ε n) ^ 6 * (J n : ℝ) ^ 4)) l (𝓝 0)) :
    Tendsto (fun n =>
      (∑ j ∈ s n, w n j * (if ‖F (p n j)‖ < ε n then 1 else 0)) / (ε n) ^ 2)
      l (𝓝 (Real.pi *
        ∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹)) :=
  Omega.Analysis.PeriodicSublevelSampling.tendsto_weighted_sublevel l q hF hperiod
    z hz hcell hzero A hA s p w hw ε (.of_forall hεpos) hε fun g hg hg' center =>
      tendsto_window_average l g hg hg' center s p w hw hw₁ ε hεpos hε
        J hJ c d hc hd hmode hc₀ hd₀ htail

#print axioms tendsto_weighted_sublevel_of_fourier

end D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling
