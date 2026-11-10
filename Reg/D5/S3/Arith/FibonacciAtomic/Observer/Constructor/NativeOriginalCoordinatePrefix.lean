import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix
import Reg.Support.DependentFamily

/-! Faithful original-readout and finite decoder registrations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalCoordinatePrefix
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix

abbrev agreementSignature : Signature where
  Params := Address
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def agreementActual : Realization agreementSignature :=
  realize agreementSignature (fun _ p X => completionReadout p X) (fun e => nomatch e)

def agreementRejected : Realization agreementSignature :=
  realize agreementSignature (fun _ p X => completionReadout (false :: p) X) (fun e => nomatch e)

abbrev agreementArena : Arena where
  signature := agreementSignature
  Law R := ∀ (s h : Nat) (U V : CompletionTree),
    (∀ p : Address, p.length ≤ h + terminalHeight s →
      completionReadout p (rho^[s] U) = completionReadout p (rho^[s] V)) →
    ∀ p : Address, p.length ≤ h → R.readout () p U = R.readout () p V

private theorem agreement_rejected : ¬ agreementArena.Law agreementRejected := by
  intro law
  have bad := law 0 0 (node (leaf true) (leaf true)) (node (leaf false) (leaf true))
    (by
      intro p hp
      have hz : terminalHeight 0 = 0 := rfl
      rw [hz] at hp
      have empty : p = [] := by simpa using hp
      subst p
      rfl) [] (by simp)
  change Reply.alpha = Reply.beta at bad
  cases bad

def agreementEvidence : Registration agreementArena (type_of% (@inverse_prefix_agreement)) where
  actual := agreementActual
  bridge := Iff.rfl
  variation := ⟨inverse_prefix_agreement, agreementRejected, agreement_rejected⟩
  sensitivity := ⟨fun i => ⟨agreementRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, agreement_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[], leaf true, leaf false, ?_⟩
    intro eq
    cases eq

noncomputable def agreementRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inverse_prefix_agreement) (Realization agreementSignature) (Address → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalCoordinatePrefix.inverse_prefix_agreement.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix.agreementEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨agreementArena⟩
  objectArena := .source ⟨agreementArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source agreementArena ⟨agreementEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize agreementSignature (fun _ p X => completionReadout p X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev decoderSignature : Signature where
  Params := Nat
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Pattern d
  Anchor := Empty
  finiteAnchor := inferInstance

def decoderActual : Realization decoderSignature :=
  realize decoderSignature (fun _ d X => cutoff d X) (fun e => nomatch e)

private def wrongPattern : (d : Nat) → Pattern d
  | 0 => ()
  | _ + 1 => .inl true

def decoderRejected : Realization decoderSignature :=
  realize decoderSignature (fun _ d _ => wrongPattern d) (fun e => nomatch e)

abbrev decoderArena : Arena where
  signature := decoderSignature
  Law R := ∀ (s d : Nat) (X : CompletionTree),
    decodePrefix s d (cutoff (terminalHeight s + d) (rho^[s] X)) = R.readout () d X

private theorem decoder_rejected : ¬ decoderArena.Law decoderRejected := by
  intro law
  have bad := law 0 1 (leaf false)
  rw [decode_prefix_correct] at bad
  change (Sum.inl false : Pattern 1) = Sum.inl true at bad
  cases bad

def decoderEvidence : Registration decoderArena (type_of% (@decode_prefix_correct)) where
  actual := decoderActual
  bridge := Iff.rfl
  variation := ⟨decode_prefix_correct, decoderRejected, decoder_rejected⟩
  sensitivity := ⟨fun i => ⟨decoderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, decoder_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1, leaf true, leaf false, ?_⟩
    intro eq
    cases eq

noncomputable def decoderRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@decode_prefix_correct) (Realization decoderSignature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalCoordinatePrefix.decode_prefix_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix.decoderEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨decoderArena⟩
  objectArena := .source ⟨decoderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source decoderArena ⟨decoderEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize decoderSignature (fun _ d X => cutoff d X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms agreementEvidence
#print axioms decoderEvidence
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalCoordinatePrefix
