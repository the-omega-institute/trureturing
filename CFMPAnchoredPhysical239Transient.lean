import CFMPOriginalNormalMoment238Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNormalDerivative435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalExteriorNativeNormal435Transient CFMPOriginalExteriorMomentArea435Transient
open CFMPOriginalPhysicalEdge237Transient CFMPOriginalNormalMoment238Transient

namespace CFMPAnchoredPhysical239Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem frame_path_geometry
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : Matrix (Fin 4) (Fin 4) ℝ) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (l : ℝ → Fin 6 → ℝ) (t : ℝ) (hl : ContinuousAt l t) (hbase : l t = l0) :
    (∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k) ∧
      (∀ᶠ s in 𝓝 t, (frame M0 (l s)).det ≠ 0) ∧
      (∀ᶠ s in 𝓝 t, ∀ i j,
        lorentz (frame M0 (l s) i) (frame M0 (l s) j) = lengthGram (l s) i j) := by
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hnear : ∀ᶠ s in 𝓝 t, good (H M0 (l s)) :=
    ((smooth_H M0).continuous.continuousAt.comp hl).eventually
      (good_open.mem_nhds (by simpa only [Function.comp_apply, Set.mem_setOf_eq, hbase] using hgood))
  refine ⟨Filter.eventually_all.mpr (fun k => ?_),?_,?_⟩
  · exact (continuousAt_pi.mp hl k).eventually
      (Ioi_mem_nhds (by simpa only [hbase] using hl0 k))
  · exact hnear.mono (fun s hs => frame_det_nonzero M0 hm0 (l s) hs)
  · exact hnear.mono (fun s hs =>
      CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows _ _
        (frame_gram M0 hm0 (l s) hs))

theorem anchored_native_negative_normal_moment_sum
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (hc : ∀ q, -1 < sourceCosine l0 q ∧ sourceCosine l0 q < 1) :
    (∑ n : Fin 20, ∫ p in faceImage l0 hl0 f n,
      -lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift p)
        (deriv (fun s => unit (l s) (frame M0 (l s)) n) t)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      -(1/2 : ℝ) * (∑ q : Fin 6, l0 q * deriv (fun s => sourceAngle (l s) q) t) := by
  subst l0
  let M : ℝ → M4 := fun s => frame M0 (l s)
  let dN : Fin 20 → Fin 4 → ℝ := fun n =>
    deriv (fun s => unit (l s) (M s) n) t
  have hMt : M t = M0 := anchored M0 hm0 (l t) hg0
  obtain ⟨hpos,hinv,hG⟩ := frame_path_geometry (l t) hl0 M0 hm0 hg0
    l t hl.continuousAt rfl
  have hN (n : Fin 20) (i : Fin 4) :
      HasDerivAt (fun s => unit (l s) (M s) n i) (dN n i) t := by
    have hn := CFMPOriginalNormalDerivative435Transient.actual_normal_derivative
      (l t) hl0 M0 hm0 hg0 f hf l dl t hl rfl n
    exact hasDerivAt_pi.mp hn.2.2.1 i
  have hfM : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial (l t) w.val) ᵥ* M t ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)) := by
    simpa only [hMt] using hf
  simpa only [M,dN] using original_native_negative_normal_moment_sum
    l M dN t hpos hinv hG hN f hfM hc

end CFMPAnchoredPhysical239Transient

run_cmd do
  let name := ``CFMPAnchoredPhysical239Transient.anchored_native_negative_normal_moment_sum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP239 anchored native normal moment absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP239 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP239 CHECKED {name} axioms={axioms}"
