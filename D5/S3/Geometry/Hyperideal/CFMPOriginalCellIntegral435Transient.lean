import D5.S3.Geometry.Hyperideal.CFMPCompactKernelIntegral435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter MeasureTheory
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient CFMPActualCellMotion435Transient
open CFMPActualNativeCellMotion435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalFrameDensity435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCellKernel435Transient CFMPCompactKernelIntegral435Transient
open CFMPCompactKernelTube435Transient (delta delta_compact timeDerivative)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPOriginalCellIntegral435Transient

theorem original_cell_integral_transport
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : ContDiffAt ℝ 1 l t) (hdl : HasDerivAt l dl t) (hbase : l t = l0) :
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let Tn : Fin 20 → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun n =>
      totalFlux M0 (D*M0⁻¹) (edgeMatrix l0 n)
        (deriv (fun s => edgeMatrix (l s) n) t) (drop (vertices l0 n 0))
        (deriv (fun s => drop (vertices (l s) n 0)) t)
    HasDerivAt
      (fun s => ∑ n : Fin 20, ∫ u in delta,
        |(edgeMatrix (l s) n).det| * originalDensity (l s) (cellPoint (l s) n u))
      (∑ n : Fin 20, ∫ u in delta, divergence (Tn n) u) t := by
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let Tn : Fin 20 → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun n =>
    totalFlux M0 (D*M0⁻¹) (edgeMatrix l0 n)
      (deriv (fun s => edgeMatrix (l s) n) t) (drop (vertices l0 n 0))
      (deriv (fun s => drop (vertices (l s) n 0)) t)
  have hbaseC1 (n : Fin 20) (u : Fin 3 → ℝ) (hu : u ∈ delta) :
      ContDiffAt ℝ 1 (kernel l n) (t,u) :=
    original_kernel_c1 l0 hl0 M0 hm0 hg0 f hf l t hl hbase n u hu
  have hIntegral := compact_kernel_integral (kernel l) t hbaseC1
  have hi (n : Fin 20) :
      HasDerivAt (fun s => ∫ u in delta, kernel l n (s,u))
        (∫ u in delta, divergence (Tn n) u) t := by
    have heq : (∫ u in delta, timeDerivative (kernel l n) (t,u)) =
        ∫ u in delta, divergence (Tn n) u := by
      apply integral_congr_ae
      apply ae_restrict_of_forall_mem delta_compact.measurableSet
      intro u hu
      have hdiff := (hbaseC1 n u hu).differentiableAt_one.hasFDerivAt
      have hline : HasDerivAt (fun r : ℝ => (r,u)) (1,(0 : Fin 3 → ℝ)) t := by
        simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
      have htime : HasDerivAt (fun s => kernel l n (s,u))
          (timeDerivative (kernel l n) (t,u)) t := by
        simpa only [Function.comp_def,timeDerivative] using hdiff.comp_hasDerivAt t hline
      have htransport := CFMPOriginalCellTransport435Transient.original_cell_transport
        l0 hl0 M0 hm0 hg0 f hf l dl t hdl hbase n u hu
      exact htime.unique (by simpa only [kernel,Tn,D] using htransport)
    rw [← heq]
    exact hIntegral n
  simpa -implicitDefEqProofs only [kernel,Tn,D] using
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 20))) (fun n _ => hi n)

end CFMPOriginalCellIntegral435Transient
