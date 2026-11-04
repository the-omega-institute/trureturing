import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the mixed canonical anticommutator. -/

namespace Reg.D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
open _root_.D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
open _root_.D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner (FullOperator fullC)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The Kronecker matrix on the right side of the mixed canonical anticommutator. -/
abbrev signature : Signature where
  Params := Σ M : ℕ, Fin M
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := FullOperator p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p j => if p.2 = j then 1 else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (M : ℕ) (i j : Fin M),
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i = r.readout () ⟨M, i⟩ j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 0 0
  rw [fullC_mixed] at he
  change (1 : FullOperator 1) = 0 at he
  exact one_ne_zero he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 0⟩, 0, 1, ?_⟩
  change (1 : FullOperator 2) ≠ 0
  exact one_ne_zero

def source_registration : Registration arena (type_of% @fullC_mixed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fullC_mixed, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fullC_mixed) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => if p.2 = j then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
