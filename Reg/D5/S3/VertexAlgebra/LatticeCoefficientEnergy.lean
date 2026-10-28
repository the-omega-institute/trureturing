import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeCoefficientEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeCoefficientEnergy
open scoped VertexOperator

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeCoefficientEnergy

structure Params where
  D : LatticeData
  energy : ℤ

abbrev signature : Signature where
  Params := Params
  State p := Carrier p.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => v ∈ grade p.D p.energy) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (m n q : ℤ) (a b : Carrier D),
    a ∈ grade D m → b ∈ grade D n →
      r.readout () ⟨D, m + n - q - 1⟩ (((Y D a)[[q]]) b)

private theorem source_bridge : (type_of% (@actual_mode_grade)) ↔ arena.Law actual := Iff.rfl

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 0 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨zeroLattice, 1⟩, 0, vacuum zeroLattice, ?_⟩
  intro h
  have hv : vacuum zeroLattice ∈ grade zeroLattice 1 :=
    Eq.mp h (Submodule.zero_mem _)
  have hz := (mem_grade_iff zeroLattice 1 _).mp hv (0,0)
    (by simp [energy])
  simpa [vacuum] using hz

def family : Registration arena (type_of% (@actual_mode_grade)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_mode_grade, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_mode_grade) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeCoefficientEnergy.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeCoefficientEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeCoefficientEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.LatticeCoefficientEnergy
