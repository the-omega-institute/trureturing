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
  Params := Σ n : Type u, n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p P => P p.2 p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (_hp : P.PosSemidef) (_ht : P.trace = 1) (i : n),
      (R.readout () ⟨n, i⟩ P).re ≤ 1

theorem actualLaw : arena.{u}.Law actual := by
  intro n _ _ P hp ht i
  exact _root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.state_diag_le_one hp ht i

theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (n := ULift.{u} Unit) (P := 1)
    Matrix.PosSemidef.one (by simp) ⟨()⟩
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Unit, ⟨()⟩⟩, 0, 1, ?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

def sourceRegistration : Registration arena.{u}
    (type_of% @state_diag_le_one.{u}) where
  actual := actual
  bridge := Iff.rfl
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
  readout := some (realize signature.{u}
    (fun _ p P => P p.2 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
