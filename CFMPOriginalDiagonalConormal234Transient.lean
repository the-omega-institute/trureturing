import CFMPOriginalAdjacentConormal233Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalExteriorMomentArea435Transient CFMPOriginalExteriorGramArea435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPOriginalBoundaryEdge229Transient
open CFMPPairedSupportConormal230Transient
open CFMPConormalIdentification231Transient (normalize normalize_positive_smul triangleVertex)
open CFMPOriginalSupportReadout232Transient
open CFMPOriginalAdjacentConormal233Transient

namespace CFMPOriginalDiagonalConormal234Transient

abbrev Space := Fin 4 → ℝ

-- The external diagonal and the internal radial-face pairing share the original index.
theorem diagonal_internal_pair (d : Fin 12) :
    CFMPOriginalFacePairing435Transient.pairTable (diagonal d) =
      (((pairs (diagonal d)).1.1, otherIndex (pairs (diagonal d)).1.2),
       ((pairs (diagonal d)).2.1, otherIndex (pairs (diagonal d)).2.2)) := by
  fin_cases d <;> rfl

theorem conormal_neg_right (N P : Space) : conormal N (-P) = -conormal N P := by
  have hn : lorentz N (-P) = -lorentz N P := by
    simp [lorentz, Fin.sum_univ_four]
  have hp : projected N (-P) = -projected N P := by
    ext i
    simp [projected, hn, smul_eq_mul]
    ring
  simp only [conormal, hn, neg_sq, hp, smul_neg]

theorem same_facet_unit (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (n m : Fin 20) (hfacet : facet n = facet m) :
    CFMPOriginalExteriorNativeNormal435Transient.unit l M n =
      CFMPOriginalExteriorNativeNormal435Transient.unit l M m := by
  let r := supportScale l n / supportScale l m
  have hr : 0 < r := div_pos (supportScale_pos l hl n) (supportScale_pos l hl m)
  have hcov : exteriorCovector l n = r • exteriorCovector l m := by
    ext k
    have hv : ∑ j : Fin 4, (Pi.single k (1 : ℝ)) j = 1 := by simp
    have hn := covector_support_readout l hl n (Pi.single k 1) hv
    have hm := covector_support_readout l hl m (Pi.single k 1) hv
    simp only [single_one_dotProduct] at hn hm
    change exteriorCovector l n k = r * exteriorCovector l m k
    rw [hn, hm, hfacet]
    dsimp only [r]
    field_simp [(supportScale_pos l hl m).ne'] <;> ring
  have hraw : CFMPOriginalExteriorNativeNormal435Transient.raw l M n =
      r • CFMPOriginalExteriorNativeNormal435Transient.raw l M m := by
    ext k
    fin_cases k <;>
      simp [CFMPOriginalExteriorNativeNormal435Transient.raw, hcov,
        Matrix.mulVec_smul, smul_eq_mul]
  change normalize (CFMPOriginalExteriorNativeNormal435Transient.raw l M n) =
    normalize (CFMPOriginalExteriorNativeNormal435Transient.raw l M m)
  rw [hraw]
  exact normalize_positive_smul _ r hr

theorem internal_vertex_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (n : Fin 20) (i j : Fin 3) :
    lorentz (vertices l n j.succ ᵥ* M)
      (CFMPOriginalInternalNormals435Transient.unit M
        (CFMPOriginalInternalNormals435Transient.A l n i)) =
      (if j = i then -|(CFMPOriginalInternalNormals435Transient.B l n).det| else 0) /
        Real.sqrt (lorentz
          (CFMPOriginalInternalNormals435Transient.raw M
            (CFMPOriginalInternalNormals435Transient.A l n i))
          (CFMPOriginalInternalNormals435Transient.raw M
            (CFMPOriginalInternalNormals435Transient.A l n i))) := by
  have he (X Y : Space) (r : ℝ) : lorentz X (r • Y) = r * lorentz X Y := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [CFMPOriginalInternalNormals435Transient.unit, he,
    CFMPOriginalInternalNormals435Transient.pair_raw M hM,
    CFMPOriginalInternalNormals435Transient.vertex_readout l hl n i j.succ]
  simp only [Fin.succ_inj, div_eq_mul_inv, mul_comm]

variable (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
include hl hM hG hf

theorem original_internal_edge_conormal (n : Fin 20) (e : Fin 3) :
    dualUnit (faceV0 l M n) (faceB l M n) (faceC l M n) e =
      conormal (CFMPOriginalExteriorNativeNormal435Transient.unit l M n)
        (CFMPOriginalInternalNormals435Transient.unit M
          (CFMPOriginalInternalNormals435Transient.A l n (otherIndex e))) := by
  have hstartIndex : CFMPConormalIdentification231Transient.startIndex = startIndex := rfl
  have hendIndex : CFMPConormalIdentification231Transient.endIndex = endIndex := rfl
  have hotherIndex : CFMPConormalIdentification231Transient.otherIndex = otherIndex := rfl
  obtain ⟨h0, hb, hc⟩ := original_face_normal_orthogonality l hl M hM hG f hf n
  have hi := CFMPOriginalInternalNormals435Transient.pair_unit l hl M hM f hf n (otherIndex e)
  have ho := CFMPOriginalExteriorNativeNormal435Transient.pair_unit l hl M hM hG f hf n
  apply CFMPConormalIdentification231Transient.dualUnit_eq_of_edge_support
    (faceV0 l M n) (faceB l M n) (faceC l M n)
    (CFMPOriginalExteriorNativeNormal435Transient.unit l M n)
    (CFMPOriginalInternalNormals435Transient.unit M
      (CFMPOriginalInternalNormals435Transient.A l n (otherIndex e))) e
    (exterior_gram_negative l hl M hM hG f hf n).ne ho hi h0 hb hc
  · rw [hstartIndex, triangle_vertex_frame, internal_vertex_readout l hl M hM]
    have h : startIndex e ≠ otherIndex e := by fin_cases e <;> decide
    rw [if_neg h, zero_div]
  · rw [hendIndex, triangle_vertex_frame, internal_vertex_readout l hl M hM]
    have h : endIndex e ≠ otherIndex e := by fin_cases e <;> decide
    rw [if_neg h, zero_div]
  · rw [hotherIndex, triangle_vertex_frame, internal_vertex_readout l hl M hM, if_pos rfl]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos (abs_pos.mpr (CFMPOriginalInternalNormals435Transient.determinant_ne l hl n)))
      (Real.sqrt_pos.mpr
        (CFMPOriginalInternalNormals435Transient.raw_spacelike l hl M hM f hf n (otherIndex e)))

theorem original_diagonal_conormals_cancel (d : Fin 12) :
    dualUnit (faceV0 l M (pairs (diagonal d)).1.1)
        (faceB l M (pairs (diagonal d)).1.1)
        (faceC l M (pairs (diagonal d)).1.1) (pairs (diagonal d)).1.2 +
      dualUnit (faceV0 l M (pairs (diagonal d)).2.1)
        (faceB l M (pairs (diagonal d)).2.1)
        (faceC l M (pairs (diagonal d)).2.1) (pairs (diagonal d)).2.2 = 0 := by
  have hi := CFMPOriginalInternalNormals435Transient.paired_normals l M (diagonal d)
  rw [diagonal_internal_pair] at hi
  have ho := same_facet_unit l hl M _ _ (diagonal_same_facet d)
  rw [original_internal_edge_conormal l hl M hM hG f hf,
    original_internal_edge_conormal l hl M hM hG f hf, ho, hi, conormal_neg_right]
  exact neg_add_cancel _

end CFMPOriginalDiagonalConormal234Transient

run_cmd do
  let name := ``CFMPOriginalDiagonalConormal234Transient.original_diagonal_conormals_cancel
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP234 original diagonal conormal cancellation absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP234 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP234 CHECKED {name} axioms={axioms}"
