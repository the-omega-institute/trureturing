import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open _root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := n → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ P i => (P i i).re) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (_hp : P.PosSemidef) (_ht : P.trace = 1) (i : n),
      (R.readout () n P) i ≤ 1

theorem actualLaw : arena.{u}.Law actual := by
  intro n _ _ P hp ht i
  exact _root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.state_diag_le_one hp ht i

theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (ULift.{u} Unit) (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
    Matrix.PosSemidef.one (by simp) ⟨()⟩
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨ULift.{u} Bool, 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun f : ULift.{u} Bool → ℝ => f ⟨false⟩) he
  change (0 : ℝ) = 1 at hc
  exact zero_ne_one hc

def sourceRegistration : Registration arena.{u}
    (type_of% @_root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.state_diag_le_one.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h n _ _ P hp ht i
      exact h hp ht i
    · intro h n _ _ P hp ht i
      exact h n P hp ht i
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.state_diag_le_one.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
