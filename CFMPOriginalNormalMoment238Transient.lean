import CFMPOriginalPhysicalEdge237Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorMomentArea435Transient
open CFMPOriginalExteriorGramArea435Transient CFMPOriginalExteriorNativeMoment435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPOriginalAdjacentConormal233Transient CFMPConormalIdentification231Transient
open CFMPOriginalDiagonalFlux235Transient CFMPOriginalPhysicalEdge237Transient

namespace CFMPOriginalNormalMoment238Transient

abbrev Space := Fin 4 → ℝ

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

variable (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Fin 20 → Space) (t : ℝ)
    (hpos : ∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k)
    (hinv : ∀ᶠ s in 𝓝 t, (M s).det ≠ 0)
    (hG : ∀ᶠ s in 𝓝 t, ∀ i j, lorentz (M s i) (M s j) = lengthGram (l s) i j)
    (hN : ∀ n i, HasDerivAt
      (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      (dN n i) t)
    (f : cutBody (l t) → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial (l t) w.val) ᵥ* M t ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
include hinv hG hN hf

theorem original_normal_derivative_moment (n : Fin 20) :
    2 * (∫ p in faceImage (l t) hpos.self_of_nhds f n,
      lorentz (lift p) (dN n)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∑ e : Fin 3, boundaryFlux (l t) hpos.self_of_nhds (M t) f dN n e := by
  have hu := CFMPOriginalExteriorNativeNormal435Transient.pair_unit
    (l t) hpos.self_of_nhds (M t) hinv.self_of_nhds hG.self_of_nhds f hf n
  have horth := actual_unit_derivative_orthogonal l M (dN n) t n (hN n) hu
  obtain ⟨h0,hb,hc⟩ := original_face_normal_orthogonality (l t) hpos.self_of_nhds
    (M t) hinv.self_of_nhds hG.self_of_nhds f hf n
  have hdet := (exterior_gram_negative (l t) hpos.self_of_nhds (M t)
    hinv.self_of_nhds hG.self_of_nhds f hf n).ne
  obtain ⟨a,ha⟩ := face_span (faceV0 (l t) (M t) n) (faceB (l t) (M t) n)
    (faceC (l t) (M t) n)
    (CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) n)
    hdet hu h0 hb hc (dN n) horth
  have hm := original_exterior_native_boundary_moment (l t) hpos.self_of_nhds
    (M t) hinv.self_of_nhds hG.self_of_nhds f hf n a
  simpa only [ha, boundaryFlux, edgeLength] using hm

theorem original_native_normal_moment_sum
    (hc : ∀ q, -1 < sourceCosine (l t) q ∧ sourceCosine (l t) q < 1) :
    2 * (∑ n : Fin 20, ∫ p in faceImage (l t) hpos.self_of_nhds f n,
      lorentz (lift p) (dN n)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∑ q : Fin 6, l t q * deriv (fun s => sourceAngle (l s) q) t := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ n : Fin 20, ∑ e : Fin 3,
        boundaryFlux (l t) hpos.self_of_nhds (M t) f dN n e := by
      apply Finset.sum_congr rfl
      intro n _
      exact original_normal_derivative_moment l M dN t hpos hinv hG hN f hf n
    _ = _ := original_boundary_length_angle_sum l M dN t hpos hinv hG hN f hf hc

-- The integrands are on the actual original native triangle images with native H2 area.
-- Connecting them to the calibrated scalar volume derivative still needs its face-velocity identity.
theorem original_native_negative_normal_moment_sum
    (hc : ∀ q, -1 < sourceCosine (l t) q ∧ sourceCosine (l t) q < 1) :
    (∑ n : Fin 20, ∫ p in faceImage (l t) hpos.self_of_nhds f n,
      -lorentz (lift p) (dN n)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      -(1/2 : ℝ) * (∑ q : Fin 6, l t q * deriv (fun s => sourceAngle (l s) q) t) := by
  have hm := original_native_normal_moment_sum l M dN t hpos hinv hG hN f hf hc
  simp_rw [integral_neg]
  rw [Finset.sum_neg_distrib]
  linarith

end CFMPOriginalNormalMoment238Transient

run_cmd do
  let name := ``CFMPOriginalNormalMoment238Transient.original_native_negative_normal_moment_sum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP238 original native negative normal moment sum absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP238 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP238 CHECKED {name} axioms={axioms}"
