import CFMPOriginalDiagonalConormal234Transient
import CFMPOriginalTruncationOrthogonal236Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeMoment435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalExteriorMomentArea435Transient CFMPOriginalExteriorGramArea435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPOriginalTriangleBoundary435Transient CFMPOriginalExteriorNativeMoment435Transient
open CFMPOriginalBoundaryEdge229Transient CFMPOriginalDiagonalConormal234Transient
open CFMPOriginalAdjacentConormal233Transient CFMPOriginalTruncationOrthogonal236Transient

namespace CFMPOriginalDiagonalFlux235Transient

abbrev Space := Fin 4 → ℝ

def edgeLength (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (n : Fin 20) (e : Fin 3) : ℝ :=
  dist (f (edgeStart (facePoints l hl n) e))
    (f (edgeEnd (facePoints l hl n) e))

theorem edgeStart_val (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (e : Fin 3) :
    (edgeStart (facePoints l hl n) e).val = startVertex l (n,e) := by
  fin_cases e <;> rfl

theorem edgeEnd_val (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (e : Fin 3) :
    (edgeEnd (facePoints l hl n) e).val = endVertex l (n,e) := by
  fin_cases e <;> rfl

-- The distances belong to the same original realization, including reversed pairs.
theorem paired_edgeLength (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (p : Fin 30) :
    edgeLength l hl f (pairs p).1.1 (pairs p).1.2 =
      edgeLength l hl f (pairs p).2.1 (pairs p).2.2 := by
  have h := paired_endpoints l p
  cases hs : swapped p with
  | false =>
    simp [hs] at h
    have hstart : edgeStart (facePoints l hl (pairs p).1.1) (pairs p).1.2 =
        edgeStart (facePoints l hl (pairs p).2.1) (pairs p).2.2 := by
      apply Subtype.ext
      simpa only [edgeStart_val] using h.1
    have hend : edgeEnd (facePoints l hl (pairs p).1.1) (pairs p).1.2 =
        edgeEnd (facePoints l hl (pairs p).2.1) (pairs p).2.2 := by
      apply Subtype.ext
      simpa only [edgeEnd_val] using h.2
    simp only [edgeLength, hstart, hend]
  | true =>
    simp [hs] at h
    have hstart : edgeStart (facePoints l hl (pairs p).1.1) (pairs p).1.2 =
        edgeEnd (facePoints l hl (pairs p).2.1) (pairs p).2.2 := by
      apply Subtype.ext
      simpa only [edgeStart_val, edgeEnd_val] using h.1
    have hend : edgeEnd (facePoints l hl (pairs p).1.1) (pairs p).1.2 =
        edgeStart (facePoints l hl (pairs p).2.1) (pairs p).2.2 := by
      apply Subtype.ext
      simpa only [edgeStart_val, edgeEnd_val] using h.2
    simp only [edgeLength, hstart, hend, dist_comm]

-- Positivity is required only near the differentiation point.
theorem same_facet_normal_derivative
    (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Fin 20 → Space) (t : ℝ)
    (hpos : ∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k)
    (hN : ∀ n i, HasDerivAt
      (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      (dN n i) t)
    (n m : Fin 20) (hfacet : facet n = facet m) : dN n = dN m := by
  ext i
  have he : (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      =ᶠ[𝓝 t] fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) m i :=
    hpos.mono (fun s hs => congrFun (same_facet_unit (l s) hs (M s) n m hfacet) i)
  exact (hN n i).unique ((hN m i).congr_of_eventuallyEq he)

theorem original_diagonal_flux_cancel
    (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Fin 20 → Space) (t : ℝ)
    (hpos : ∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k)
    (hN : ∀ n i, HasDerivAt
      (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      (dN n i) t)
    (hM : (M t).det ≠ 0)
    (hG : ∀ i j, lorentz (M t i) (M t j) = lengthGram (l t) i j)
    (f : cutBody (l t) → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial (l t) w.val) ᵥ* M t ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (d : Fin 12) :
    let hl := hpos.self_of_nhds
    lorentz (dN (pairs (diagonal d)).1.1)
        (dualUnit (faceV0 (l t) (M t) (pairs (diagonal d)).1.1)
          (faceB (l t) (M t) (pairs (diagonal d)).1.1)
          (faceC (l t) (M t) (pairs (diagonal d)).1.1) (pairs (diagonal d)).1.2) *
        edgeLength (l t) hl f (pairs (diagonal d)).1.1 (pairs (diagonal d)).1.2 +
      lorentz (dN (pairs (diagonal d)).2.1)
        (dualUnit (faceV0 (l t) (M t) (pairs (diagonal d)).2.1)
          (faceB (l t) (M t) (pairs (diagonal d)).2.1)
          (faceC (l t) (M t) (pairs (diagonal d)).2.1) (pairs (diagonal d)).2.2) *
        edgeLength (l t) hl f (pairs (diagonal d)).2.1 (pairs (diagonal d)).2.2 = 0 := by
  dsimp only
  have hderiv := same_facet_normal_derivative l M dN t hpos hN _ _ (diagonal_same_facet d)
  have hconormal := original_diagonal_conormals_cancel (l t) hpos.self_of_nhds
    (M t) hM hG f hf d
  have hsum := congrArg (lorentz (dN (pairs (diagonal d)).2.1)) hconormal
  have hadd (X Y Z : Space) : lorentz X (Y+Z) = lorentz X Y + lorentz X Z := by
    simp [lorentz, Fin.sum_univ_four]
    ring
  rw [hadd] at hsum
  have hz (X : Space) : lorentz X 0 = 0 := by simp [lorentz]
  rw [hz] at hsum
  rw [hderiv, paired_edgeLength (l t) hpos.self_of_nhds f (diagonal d)]
  rw [← add_mul, hsum, zero_mul]

def boundaryFlux (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (dN : Fin 20 → Space) (n : Fin 20) (e : Fin 3) : ℝ :=
  lorentz (dN n) (dualUnit (faceV0 l M n) (faceB l M n) (faceC l M n) e) *
    edgeLength l hl f n e

section BoundaryReduction

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

theorem original_truncation_flux_cancel (a : Fin 12) :
    boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
        (pairs (truncation a)).1.1 (pairs (truncation a)).1.2 +
      boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
        (pairs (truncation a)).2.1 (pairs (truncation a)).2.2 = 0 := by
  have hne : facet (pairs (truncation a)).1.1 ≠ facet (pairs (truncation a)).2.1 := by
    fin_cases a <;> decide
  have hc := original_adjacent_conormals (l t) hpos.self_of_nhds (M t)
    hinv.self_of_nhds hG.self_of_nhds f hf (truncation a) hne
  have hz := original_truncation_derivative_readout l M dN t hpos hinv hG hN a
  unfold boundaryFlux
  rw [hc.1, hc.2, paired_edgeLength (l t) hpos.self_of_nhds f (truncation a),
    ← add_mul, hz, zero_mul]

-- The original sixty triangle terms reduce to the six physical paired-edge terms.
-- The remaining physical angle and original length identifications are separate.
theorem original_boundary_flux_reduce :
    (∑ n : Fin 20, ∑ e : Fin 3,
      boundaryFlux (l t) hpos.self_of_nhds (M t) f dN n e) =
      ∑ q : Fin 6,
        (boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
            (pairs (physical q)).1.1 (pairs (physical q)).1.2 +
          boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
            (pairs (physical q)).2.1 (pairs (physical q)).2.2) := by
  apply boundary_sum_reduce
  · intro d
    exact original_diagonal_flux_cancel l M dN t hpos hN
      hinv.self_of_nhds hG.self_of_nhds f hf d
  · exact original_truncation_flux_cancel l M dN t hpos hinv hG hN f hf
  · intro q
    rfl

end BoundaryReduction

end CFMPOriginalDiagonalFlux235Transient

run_cmd do
  let name := ``CFMPOriginalDiagonalFlux235Transient.original_boundary_flux_reduce
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP235 original boundary flux reduction absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP235 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP235 CHECKED {name} axioms={axioms}"
