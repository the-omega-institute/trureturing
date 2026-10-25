import CFMPAnchoredPhysical239Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNormalSpeedDerivative435Transient

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
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredOriginalExteriorFaceMotion435Transient CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPOriginalPhysicalEdge237Transient CFMPAnchoredPhysical239Transient

namespace CFMPOriginalTraceSchlafli240Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_trace_length_angle_sum
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
    (hc : ∀ q, -1 < sourceCosine l0 q ∧ sourceCosine l0 q < 1)
    (Phi : Fin 20 → HyperbolicThreeSpace → ℝ)
    (hPhi : ∀ n, IntegrableOn (Phi n) (faceImage l0 hl0 f n)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace))
    (htrace : ∀ (n : Fin 20) (q : parameterTriangle),
      dotProduct (deriv (fun s => nativeMap
        (ambient (frame M0 (l s)) (facePoint (l s) n q.val))) t)
        (coordinateNormal (nativeCoordinates
          (f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩))
          (unit l0 M0 n)) /
        (nativeCoordinates
          (f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩) 2)^2 =
        Phi n (f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩)) :
    (∑ n : Fin 20, ∫ p in faceImage l0 hl0 f n, Phi n p
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      -(1/2 : ℝ) * (∑ q : Fin 6, l0 q * deriv (fun s => sourceAngle (l s) q) t) := by
  let dN : Fin 20 → Fin 4 → ℝ := fun n =>
    deriv (fun s => unit (l s) (frame M0 (l s)) n) t
  have hpoint (n : Fin 20) (q : parameterTriangle) :
      Phi n (f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩) =
      -lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift
        (f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩)) (dN n) := by
    have hs := CFMPOriginalNormalSpeedDerivative435Transient.actual_normal_speed_derivative
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n q.val q.property
    exact (htrace n q).symm.trans hs.2.2
  have hrows := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  have hrow (n : Fin 20) :
      (∫ p in faceImage l0 hl0 f n, Phi n p
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      (∫ p in faceImage l0 hl0 f n,
        -lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift p) (dN n)
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) := by
    obtain ⟨rho,P,r,D,hrho,hP,hpos,hmap,hgeometry,hmeasure,hrho',hsub⟩ :=
      CFMPOriginalExteriorCofactorSurface435Transient.original_exterior_native_cofactor_surface
        l0 hl0 M0 hm0 hrows f hf n
    have hneg : IntegrableOn
        (fun p : HyperbolicThreeSpace =>
          -lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift p) (dN n))
        (faceImage l0 hl0 f n)
        (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) :=
      (original_exterior_moment_integrable
        l0 hl0 M0 hm0 hrows f hf n (dN n)).neg
    dsimp only [faceImage]
    rw [(hsub _ (hPhi n)).2,(hsub _ hneg).2]
    apply setIntegral_congr_fun
      CFMPNativePlaneFiniteArea435Transient.referenceTriangle_compact.measurableSet
    intro q hq
    change rho q * Phi n (P q) =
      rho q * (-lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift (P q)) (dN n))
    rw [hmap q hq]
    exact congrArg (fun a : ℝ => rho q * a) (hpoint n ⟨q,hq⟩)
  calc
    _ = ∑ n : Fin 20, ∫ p in faceImage l0 hl0 f n,
        -lorentz (D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.lift p) (dN n)
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) :=
      Finset.sum_congr rfl (fun n _ => hrow n)
    _ = _ := anchored_native_negative_normal_moment_sum
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase hc

end CFMPOriginalTraceSchlafli240Transient

run_cmd do
  let name := ``CFMPOriginalTraceSchlafli240Transient.anchored_trace_length_angle_sum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP240 actual trace length-angle sum absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP240 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP240 CHECKED {name} axioms={axioms}"
