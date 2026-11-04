import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

/-! Faithful coefficient-family audit attempt for all-state truncation.
The typed family uses the complete original D,s,x telescope. Its readout is
an actual original coefficient, not a closed theorem truth value. The scoped
report decides source binding; this source does not assert declared validation.
The remaining public laws need their own faithful source-bound audits.
Underlying source-selection gap: https://github.com/the-omega-institute/trureturing/issues/25387.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct VertexOperator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostStateField
open _root_.Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (state_nontrivial zeroLattice)
open private identity_modes from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateField.Truncation

abbrev signature : Signature where
  Params := Σ D : LatticeData, State D × State D
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := State p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def nonzero (D : LatticeData) : State D := by
  letI : Nontrivial (State D) := state_nontrivial D
  exact Classical.choose (exists_ne (0 : State D))

private theorem nonzero_ne (D : LatticeData) : nonzero D ≠ 0 := by
  letI : Nontrivial (State D) := state_nontrivial D
  exact Classical.choose_spec (exists_ne (0 : State D))

def actual : Realization signature := realize signature
  (fun _ p n => ((Y p.1 p.2.1)[[n]]) p.2.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p _ => nonzero p.1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (s x : State D),
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → R.readout () ⟨D,s,x⟩ n = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := h zeroLattice 0 0
  exact nonzero_ne zeroLattice (hN N (le_refl _))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  letI : Nontrivial (State zeroLattice) := state_nontrivial zeroLattice
  obtain ⟨x, hx⟩ := exists_ne (0 : State zeroLattice)
  refine ⟨⟨zeroLattice, vacuum zeroLattice, x⟩, -1, 0, ?_⟩
  change ((Y zeroLattice (vacuum zeroLattice))[[-1]]) x ≠
    ((Y zeroLattice (vacuum zeroLattice))[[0]]) x
  rw [(stateField_vacuum_creation zeroLattice).1]
  simpa only [identity_modes, ite_true, show (0 : ℤ) ≠ -1 by decide, ite_false,
    LinearMap.id_apply, LinearMap.zero_apply] using hx

def family : Registration arena (type_of% @stateField_truncation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_truncation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stateField_truncation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateField.Truncation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateField.Truncation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => ((Y p.1 p.2.1)[[n]]) p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeMatterGhostStateField
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateField.Truncation
