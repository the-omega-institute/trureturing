import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import Reg.Support.DependentFamily

/-! Source-bound audit of the permutation equality for involutions. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing

open _root_.D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State x := Equiv.Perm x
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ x := Equiv.Perm x → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {x : Type u} (p : Equiv.Perm x), Function.Involutive p →
    r.readout () x (p * p) 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (1 : Equiv.Perm (ULift.{u} Unit)) (fun _ => rfl) (one_mul 1)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  refine ⟨ULift.{u} Bool, 1, Equiv.swap a b, ?_⟩
  intro h
  have he : Equiv.swap a b = 1 := (congrFun h 1).mp rfl
  have hab : b = a := by simpa [a, b] using congrArg (fun p => p a) he
  exact Bool.noConfusion (congrArg ULift.down hab)

def source_registration : Registration arena.{u} (type_of% @square_of_involutive.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨square_of_involutive, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@square_of_involutive.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
