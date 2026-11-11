import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Result
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer (degree place)
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice (integerWeightedSum)
open _root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent (row)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private triple
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Result

abbrev signature : Signature where
  Params := Σ r : ℕ, Module.Basis (UpperIndex r) ℤ (LinearMap.ker (integerWeightedSum r))
  State p := UpperIndex p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (3*degree p.1) → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => (p.2 k).val) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ,
    ∃ b : Module.Basis (UpperIndex r) ℤ (LinearMap.ker (integerWeightedSum r)),
      ∀ k, R.readout () ⟨r,b⟩ k=row (selectedMask r k)

private def k0 : UpperIndex 0 := .inr (.inr (.inr 0))
private def k1 : UpperIndex 0 := .inr (.inr (.inr 1))
private def i0 : Fin (3*degree 0) := place 0 ⟨0,by decide⟩

private theorem row_difference : row (selectedMask 0 k0) i0 ≠ row (selectedMask 0 k1) i0 := by
  norm_num [k0,k1,i0,selectedMask,terminalMask,triple,row,place,degree]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨b,hb⟩ := h 0
  have he := congrFun (hb k0) i0
  norm_num [rejected,realize,k0,i0,selectedMask,terminalMask,triple,row,place,degree] at he
  change (0 : ℤ)=1 at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨b,hb⟩ := actual_selected_upper_integer_basis 0
  refine ⟨⟨0,b⟩,k0,k1,?_⟩
  intro he
  have hv := congrFun he i0
  change (b k0).val i0=(b k1).val i0 at hv
  rw [hb k0,hb k1] at hv
  exact row_difference hv

def basis_family : Registration arena (type_of% (@actual_selected_upper_integer_basis)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_selected_upper_integer_basis,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def basis_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_selected_upper_integer_basis) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.actual_selected_upper_integer_basis.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Result.basis_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨basis_family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => (p.2 k).val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Result
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","arg","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis.Result
