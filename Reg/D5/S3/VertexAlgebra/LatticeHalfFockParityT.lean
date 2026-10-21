import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockParityT

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockParityT
open scoped TensorProduct

noncomputable section

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have hd : hyperbolic.G.det = -1 := by
    change Matrix.det (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = -1
    norm_num [Matrix.det_fin_two]
  rw [hd]
  exact isUnit_neg_one

private def gradeOneIndex : ActualGradeIndex hyperbolic hyperbolic_unit 1 :=
  (⟨Finsupp.single ((0 : Fin 2), 0) 1, by
    simp [oddWeight, Finsupp.weight_single, omega]⟩, 0)

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  N : ℕ

abbrev signature : Signature where
  Params := Params
  State p := actualGrade p.D p.hu p.N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => actualParity p.D p.hu (v : ActualTensor p.D p.hu))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (v : actualGrade D hu N),
    readout.readout () ⟨D, hu, N⟩ v =
      ((-1 : ℂ) ^ N) • (v : ActualTensor D hu)

theorem actual_law : arena.Law actual := by
  intro D hu N v
  exact actualParity_on_actualGrade D hu N v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h hyperbolic hyperbolic_unit 1
    (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex)
  have hn := (actualGradeBasis hyperbolic hyperbolic_unit 1).ne_zero gradeOneIndex
  have hz' : (0 : ActualTensor hyperbolic hyperbolic_unit) =
      (-1 : ℂ) • (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex :
        ActualTensor hyperbolic hyperbolic_unit) := by
    simpa [rejected, realize] using hz
  exact hn (by simpa using hz'.symm)

def familyRegistration : Registration arena (type_of% (@actualParity_on_actualGrade)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro role
    refine ⟨⟨hyperbolic, hyperbolic_unit, 1⟩, 0,
      actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex, ?_⟩
    intro h
    have hn := (actualGradeBasis hyperbolic hyperbolic_unit 1).ne_zero gradeOneIndex
    change actualParity hyperbolic hyperbolic_unit (0 : ActualTensor hyperbolic hyperbolic_unit) =
      actualParity hyperbolic hyperbolic_unit
        (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex :
          ActualTensor hyperbolic hyperbolic_unit) at h
    rw [map_zero, actualParity_on_grade_basis] at h
    simp only [pow_one, neg_smul] at h
    exact hn (by simpa using h.symm)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualParity_on_actualGrade)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockParityT.actualParity_on_actualGrade.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockParityT
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms registration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT
