import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  u : ℤ
  v : ℤ
  y : ActualTensor D hu

abbrev signature : Signature where
  Params := Params
  State p := ActualTensor p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => actualForm p.D p.hu x p.y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (u v : ℤ) (x y : ActualTensor D hu),
    actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (u : ℂ) / 2) • x →
    actualTensorL0 D hu y = ((D.rank : ℂ) / 16 + (v : ℂ) / 2) • y →
    u ≠ v → readout.readout () ⟨D, hu, u, v, y⟩ x = 0

theorem actual_law : arena.Law actual := by
  intro D hu u v x y hx hy hne
  exact actualForm_oddGrade_orthogonal D hu u v x y hx hy hne

private def emptyLattice : LatticeData where
  rank := 0
  G := 1
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem empty_unit : IsUnit emptyLattice.G.det := by
  change IsUnit (Matrix.det (1 : Matrix (Fin 0) (Fin 0) ℤ))
  rw [Matrix.det_one]
  exact isUnit_one

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h emptyLattice empty_unit 0 1 0 0 (by simp) (by simp) (by decide)
  exact one_ne_zero hz

def familyRegistration : Registration arena (type_of% (@actualForm_oddGrade_orthogonal)) where
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
    let y := actualAmbientBasis emptyLattice empty_unit (0, 0)
    have hy : y ≠ 0 := (actualAmbientBasis emptyLattice empty_unit).ne_zero (0, 0)
    obtain ⟨x, hx⟩ : ∃ x, actualForm emptyLattice empty_unit x y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hy ((actualForm_nondegenerate emptyLattice empty_unit).2 y hn)
    refine ⟨⟨emptyLattice, empty_unit, 0, 1, y⟩, x, 0, ?_⟩
    simpa [actual, realize] using hx

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualForm_oddGrade_orthogonal)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality.actualForm_oddGrade_orthogonal.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms registration

end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality
