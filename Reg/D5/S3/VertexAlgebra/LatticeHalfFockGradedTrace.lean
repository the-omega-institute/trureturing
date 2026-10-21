import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  N : ℕ

abbrev signature : Signature where
  Params := Params
  State p := ActualTensor p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => v ∈ actualGrade p.D p.hu p.N) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) (v : ActualTensor D hu),
    readout.readout () ⟨D,hu,N⟩ v ↔
      ∀ ib ∈ ((actualAmbientBasis D hu).repr v).support, oddWeight D ib.1 = N

private theorem source_bridge :
    (type_of% (@actual_grade_mem_iff_repr_support)) ↔ arena.Law actual := Iff.rfl

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0,rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have hd : hyperbolic.G.det = -1 := by
    change Matrix.det (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = -1
    norm_num [Matrix.det_fin_two]
  rw [hd]
  exact isUnit_neg_one

private def vacuum : ActualTensor hyperbolic hyperbolic_unit :=
  actualAmbientBasis hyperbolic hyperbolic_unit (0,0)

private theorem vacuum_not_grade_one :
    vacuum ∉ actualGrade hyperbolic hyperbolic_unit 1 := by
  intro hv
  have hs := (actual_grade_mem_iff_repr_support hyperbolic hyperbolic_unit 1 vacuum).mp hv
  have hm : (0,0) ∈ ((actualAmbientBasis hyperbolic hyperbolic_unit).repr vacuum).support := by
    simp [vacuum]
  have h := hs (0,0) hm
  norm_num [oddWeight] at h

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h hyperbolic hyperbolic_unit 0 0).mpr (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic,hyperbolic_unit,1⟩, 0, vacuum, ?_⟩
  intro h
  apply vacuum_not_grade_one
  exact Eq.mp h (Submodule.zero_mem _)

def familyRegistration : Registration arena (type_of% (@actual_grade_mem_iff_repr_support)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_grade_mem_iff_repr_support, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_grade_mem_iff_repr_support)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace.actual_grade_mem_iff_repr_support.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
