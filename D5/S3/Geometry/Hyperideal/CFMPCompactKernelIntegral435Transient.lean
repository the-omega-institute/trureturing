import D5.S3.Geometry.Hyperideal.CFMPCompactKernelTube435Transient
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open CFMPCompactKernelTube435Transient

namespace CFMPCompactKernelIntegral435Transient

theorem compact_kernel_integral (F : Fin 20 → ℝ × V → ℝ) (t : ℝ)
    (hbase : ∀ n u, u ∈ delta → ContDiffAt ℝ 1 (F n) (t,u)) :
    ∀ n, HasDerivAt (fun s => ∫ u in delta, F n (s,u))
      (∫ u in delta, timeDerivative (F n) (t,u)) t := by
  obtain ⟨ε,hε,_,hall⟩ := compact_c1_tube F t univ isOpen_univ (mem_univ t) hbase
  have ht : t ∈ Icc (t-ε) (t+ε) := by constructor <;> linarith
  have hnhds : Ioo (t-ε) (t+ε) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  intro n
  obtain ⟨hF,hD,hd,C,hC⟩ := hall n
  have hslice (s : ℝ) (hs : s ∈ Icc (t-ε) (t+ε)) :
      ContinuousOn (fun u : V => F n (s,u)) delta :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hs,hu⟩)
  have hDslice : ContinuousOn (fun u : V => timeDerivative (F n) (t,u)) delta :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨ht,hu⟩)
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun u : V => F n (s,u)) (volume.restrict delta) := by
    filter_upwards [hnhds] with s hs
    exact (hslice s (Ioo_subset_Icc_self hs)).aestronglyMeasurable delta_compact.measurableSet
  have hbound : ∀ᵐ u ∂volume.restrict delta,
      ∀ s ∈ Ioo (t-ε) (t+ε), ‖timeDerivative (F n) (s,u)‖ ≤ C := by
    apply ae_restrict_of_forall_mem delta_compact.measurableSet
    intro u hu s hs
    exact hC (s,u) ⟨Ioo_subset_Icc_self hs,hu⟩
  have hdiff : ∀ᵐ u ∂volume.restrict delta,
      ∀ s ∈ Ioo (t-ε) (t+ε),
        HasDerivAt (fun r => F n (r,u)) (timeDerivative (F n) (s,u)) s := by
    apply ae_restrict_of_forall_mem delta_compact.measurableSet
    intro u hu s hs
    exact hd s (Ioo_subset_Icc_self hs) u hu
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnhds hmeas
    ((hslice t ht).integrableOn_compact delta_compact)
    (hDslice.aestronglyMeasurable delta_compact.measurableSet)
    hbound (integrableOn_const delta_compact.measure_ne_top) hdiff).2

end CFMPCompactKernelIntegral435Transient
