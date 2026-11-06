import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent

/-! Typed source-family audit attempts for the literal current and all-mode
covariance. The scoped binding report determines their assessment status. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct VertexOperator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostStateField
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostDegree
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostNumberCurrent
open _root_.Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent

namespace number_current_zero_mode
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (p : signature.Params) : signature.State p :=
  ((Y p (numberCurrent p)) [[0]])
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData), R.readout () D (tensorNumber D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice
def family : Registration arena (type_of% @number_current_zero_mode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨number_current_zero_mode, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    letI := state_nontrivial zeroLattice
    let p : signature.Params := zeroLattice
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@number_current_zero_mode) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent.number_current_zero_mode.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent.number_current_zero_mode.family
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
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostNumberCurrent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end number_current_zero_mode

namespace tensorNumber_stateField
abbrev signature : Signature where
  Params := Σ D : LatticeData, State D × State D × ℤ
  State p := State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (p : signature.Params) : signature.State p :=
  tensorNumber p.1 (((Y p.1 p.2.1) [[p.2.2.2]]) p.2.2.1) -
    ((Y p.1 p.2.1) [[p.2.2.2]]) (tensorNumber p.1 p.2.2.1)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (a x : State D) (n : ℤ), R.readout () ⟨D,a,x,n⟩ (((Y D (tensorNumber D a)) [[n]]) x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 0
def family : Registration arena (type_of% @tensorNumber_stateField) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensorNumber_stateField, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    letI := state_nontrivial zeroLattice
    let p : signature.Params := ⟨zeroLattice,0,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensorNumber_stateField) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent.tensorNumber_stateField.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent.tensorNumber_stateField.family
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
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostNumberCurrent
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tensorNumber_stateField

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostNumberCurrent
