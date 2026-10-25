import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorGramArea435Transient
import CFMPConormalIdentification231Transient
import CFMPOriginalSupportReadout232Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPOriginalExteriorNativeNormal435Transient
open CFMPOriginalExteriorMomentArea435Transient
open CFMPOriginalExteriorGramArea435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPOriginalBoundaryEdge229Transient
open CFMPPairedSupportConormal230Transient
open CFMPConormalIdentification231Transient (triangleVertex)
open CFMPOriginalSupportReadout232Transient

namespace CFMPOriginalAdjacentConormal233Transient

abbrev Space := Fin 4 → ℝ

theorem triangle_vertex_frame (l : Fin 6 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) (j : Fin 3) :
    triangleVertex (faceV0 l M n) (faceB l M n) (faceC l M n) j =
      vertices l n j.succ ᵥ* M := by
  fin_cases j <;>
    simp [triangleVertex, faceV0, faceB, faceC, base, direction, Matrix.sub_vecMul] <;> module

variable (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
include hl hM hG hf

theorem original_face_normal_orthogonality (n : Fin 20) :
    lorentz (faceV0 l M n) (unit l M n) = 0 ∧
    lorentz (faceB l M n) (unit l M n) = 0 ∧
    lorentz (faceC l M n) (unit l M n) = 0 := by
  have hown (j : Fin 3) : lorentz (vertices l n j.succ ᵥ* M) (unit l M n) = 0 := by
    rw [unit_support_readout l hl M hM n _ (vertex_sum_one l hl n j.succ),
      exterior_vertices_support l hl n j, mul_zero]
  have hadd (X Y : Space) : lorentz (X+Y) (unit l M n) =
      lorentz X (unit l M n) + lorentz Y (unit l M n) := by
    simp [lorentz, Fin.sum_univ_four]
    ring
  have h0 : lorentz (faceV0 l M n) (unit l M n) = 0 := by
    simpa [faceV0, base] using hown 0
  have hb : lorentz (faceB l M n) (unit l M n) = 0 := by
    have h := hown 1
    rw [← triangle_vertex_frame l M n 1] at h
    change lorentz (faceV0 l M n + faceB l M n) (unit l M n) = 0 at h
    simpa [hadd, h0] using h
  have hc : lorentz (faceC l M n) (unit l M n) = 0 := by
    have h := hown 2
    rw [← triangle_vertex_frame l M n 2] at h
    change lorentz (faceV0 l M n + faceC l M n) (unit l M n) = 0 at h
    simpa [hadd, h0] using h
  exact ⟨h0, hb, hc⟩

theorem one_sided_original_conormal (n m : Fin 20) (e : Fin 3)
    (hstart : incident (facet m) (labels n (startIndex e)).1 (labels n (startIndex e)).2)
    (hend : incident (facet m) (labels n (endIndex e)).1 (labels n (endIndex e)).2)
    (hinside : ¬incident (facet m) (labels n (otherIndex e)).1 (labels n (otherIndex e)).2) :
    dualUnit (faceV0 l M n) (faceB l M n) (faceC l M n) e =
      conormal (unit l M n) (unit l M m) := by
  have hraw (k : Fin 20) := raw_spacelike l hl M hM hG f hf k
  have hnorm (k : Fin 20) := pair_unit l hl M hM hG f hf k
  have hdet := (exterior_gram_negative l hl M hM hG f hf n).ne
  obtain ⟨h0, hb, hc⟩ := original_face_normal_orthogonality l hl M hM hG f hf n
  apply CFMPConormalIdentification231Transient.dualUnit_eq_of_edge_support
    (faceV0 l M n) (faceB l M n) (faceC l M n) (unit l M n) (unit l M m) e
    hdet (hnorm n) (hnorm m) h0 hb hc
  · rw [triangle_vertex_frame]
    exact (vertex_support_signs l hl M hM n m (startIndex e) (hraw m)).1 hstart
  · rw [triangle_vertex_frame]
    exact (vertex_support_signs l hl M hM n m (endIndex e) (hraw m)).1 hend
  · rw [triangle_vertex_frame]
    exact (vertex_support_signs l hl M hM n m (otherIndex e) (hraw m)).2 hinside

-- All 18 non-coplanar pairs use their actual triangles, normals, and endpoint supports.
theorem original_adjacent_conormals (p : Fin 30)
    (hne : facet (pairs p).1.1 ≠ facet (pairs p).2.1) :
    dualUnit (faceV0 l M (pairs p).1.1) (faceB l M (pairs p).1.1)
        (faceC l M (pairs p).1.1) (pairs p).1.2 =
      conormal (unit l M (pairs p).1.1) (unit l M (pairs p).2.1) ∧
    dualUnit (faceV0 l M (pairs p).2.1) (faceB l M (pairs p).2.1)
        (faceC l M (pairs p).2.1) (pairs p).2.2 =
      conormal (unit l M (pairs p).2.1) (unit l M (pairs p).1.1) := by
  obtain ⟨ha, hb⟩ := adjacent_support_incidence p hne
  exact ⟨one_sided_original_conormal l hl M hM hG f hf _ _ _ ha.1 ha.2.1 ha.2.2,
    one_sided_original_conormal l hl M hM hG f hf _ _ _ hb.1 hb.2.1 hb.2.2⟩

end CFMPOriginalAdjacentConormal233Transient

run_cmd do
  let name := ``CFMPOriginalAdjacentConormal233Transient.original_adjacent_conormals
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP233 actual adjacent conormals absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP233 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP233 CHECKED {name} axioms={axioms}"
