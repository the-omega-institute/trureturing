import CFMPGenericInteriorTopology1460Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Hyperideal.ActualCornerTransport (faceVertex)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate
open Topology Set

abbrev OpenTriangle := {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

def bary (j : Fin 4) (p : ℝ × ℝ) (i : Fin 4) : ℝ :=
  if i = faceVertex j 0 then p.1
  else if i = faceVertex j 1 then p.2
  else if i = faceVertex j 2 then 1 - p.1 - p.2 else 0

theorem bary_values (j : Fin 4) (p : ℝ × ℝ) :
    bary j p j = 0 ∧ bary j p (faceVertex j 0) = p.1 ∧
      bary j p (faceVertex j 1) = p.2 ∧
      bary j p (faceVertex j 2) = 1 - p.1 - p.2 := by
  fin_cases j <;> simp [bary,faceVertex]

theorem bary_simplex (j : Fin 4) (p : OpenTriangle) :
    (∀ i, 0 ≤ bary j p.val i) ∧ (∑ i, bary j p.val i) = 1 ∧
      (∀ i, i ≠ j → bary j p.val i ≠ 0) := by
  obtain ⟨hu,hv,hs⟩ := p.property
  refine ⟨?_,?_,?_⟩
  · intro i
    unfold bary
    split_ifs <;> linarith
  · fin_cases j <;> simp [bary,faceVertex,Fin.sum_univ_succ] <;> ring
  · intro i hij
    fin_cases j <;> fin_cases i <;>
      simp [bary,faceVertex] at * <;> linarith

theorem bary_inverse (j : Fin 4) (a : Fin 4 → ℝ)
    (hj : a j = 0) (hs : (∑ i, a i) = 1) :
    bary j (a (faceVertex j 0),a (faceVertex j 1)) = a := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [bary,faceVertex,Fin.sum_univ_succ] at * <;> linarith

variable {T : Type*} [TopologicalSpace T] [DiscreteTopology T]

def interiorPoint (P : RawFacePairing T) (ν : Vertex P) (t : T) (j : Fin 4)
    (hc : label P (t,j) = ν) (p : OpenTriangle) : ↥(InteriorPatch P ν (t,j)) := by
  have hb := bary_simplex j p
  refine ⟨⟨((t,j),bary j p.val),?_,hb.1,hb.2.1,hc⟩,rfl,?_⟩
  · exact (bary_values j p.val).1
  · exact hb.2.2

def pointCoordinates (P : RawFacePairing T) (ν : Vertex P) (t : T) (j : Fin 4)
    (x : ↥(InteriorPatch P ν (t,j))) : OpenTriangle := by
  let a := x.val.val.2
  have htag : x.val.val.1 = (t,j) := x.property.1
  have hj : a j = 0 := by
    have h := x.val.property.1
    rw [htag] at h
    exact h
  have hp : ∀ r : Fin 3, 0 < a (faceVertex j r) := by
    intro r
    have hn := x.val.property.2.1 (faceVertex j r)
    have hne : faceVertex j r ≠ x.val.val.1.2 := by
      rw [htag]
      fin_cases j <;> fin_cases r <;> simp [faceVertex]
    have hnz := x.property.2 (faceVertex j r) hne
    exact lt_of_le_of_ne hn hnz.symm
  refine ⟨(a (faceVertex j 0),a (faceVertex j 1)),hp 0,hp 1,?_⟩
  have hs := x.val.property.2.2.1
  change (∑ i, a i) = 1 at hs
  have hsum : a (faceVertex j 0) + a (faceVertex j 1) + a (faceVertex j 2) = 1 := by
    fin_cases j <;> simp [faceVertex,Fin.sum_univ_succ] at * <;> linarith
  have hpos := hp 2
  linarith

def originalInteriorCoordinates (P : RawFacePairing T) (ν : Vertex P) (t : T) (j : Fin 4)
    (hc : label P (t,j) = ν) : OpenTriangle ≃ₜ ↥(InteriorPatch P ν (t,j)) where
  toFun := interiorPoint P ν t j hc
  invFun := pointCoordinates P ν t j
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (bary_values j p.val).2.1 (bary_values j p.val).2.2.1
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.1.symm
    · change bary j (x.val.val.2 (faceVertex j 0),x.val.val.2 (faceVertex j 1)) = x.val.val.2
      have hj := x.val.property.1
      rw [x.property.1] at hj
      exact bary_inverse j x.val.val.2 hj x.val.property.2.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply continuous_pi
    intro i
    change Continuous (fun p : OpenTriangle => bary j p.val i)
    unfold bary
    split_ifs <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply (faceVertex j 0)).comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))).prodMk
      ((continuous_apply (faceVertex j 1)).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))

theorem open_triangle_domain : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1} := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))

def originalInteriorChart (P : RawFacePairing T) (ν : Vertex P) (t : T) (j : Fin 4)
    (hc : label P (t,j) = ν) :
    OpenTriangle ≃ₜ ↥(quotientInteriorPatch P ν (t,j)) :=
  (originalInteriorCoordinates P ν t j hc).trans (originalInteriorPatchHomeomorph P ν (t,j))

end D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.bary_values,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.bary_simplex,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.bary_inverse,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.originalInteriorCoordinates,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.open_triangle_domain,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorChart1466Candidate.originalInteriorChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1466 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1466 disallowed {ax}"
    Lean.logInfo m!"CFMP1466 CHECKED {name} axioms={axioms}"
