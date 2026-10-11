import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder

abbrev decoderSignature : Signature where
  Params := CutSet × CutSet × CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def decoderActual : Realization decoderSignature :=
  realize decoderSignature
    (fun _ p u => rowDecoder p.2.1 (canonicalRow p.1 u)) (fun e => nomatch e)

def decoderRejected : Realization decoderSignature :=
  realize decoderSignature (fun _ _ _ => .of (.inl false)) (fun e => nomatch e)

abbrev decoderArena : Arena where
  signature := decoderSignature
  Law R := ∀ (P Q S : CutSet), CutPrefixFree P → CutPrefixFree Q →
    (∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s) →
    ∀ u : Source, R.readout () (P, Q, S) u = canonicalRow Q u

private theorem empty_prefixFree : CutPrefixFree (∅ : CutSet) := by
  intro p hp
  simp at hp

private theorem decoder_rejected_law : ¬ decoderArena.Law decoderRejected := by
  intro h
  have impossible := h ∅ ∅ ∅ empty_prefixFree empty_prefixFree
    (by intro p; simp) (.of true)
  change FreeMagma.of (Sum.inl false : Bool ⊕ Nat) = .of (.inl true) at impossible
  cases impossible

def decoderProof : Registration decoderArena
    (∀ (P Q S : CutSet) (_ : CutPrefixFree P) (_ : CutPrefixFree Q),
      (∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s) →
      ∀ u : Source, rowDecoder Q (canonicalRow P u) = canonicalRow Q u) where
  actual := decoderActual
  bridge := Iff.rfl
  variation := ⟨commonSuffix_decoder_correct, decoderRejected, decoder_rejected_law⟩
  sensitivity := ⟨fun i => ⟨decoderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, decoder_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(∅, ∅, ∅), .of true, .of false, ?_⟩
    change rowDecoder ∅ (canonicalRow ∅ (.of true)) ≠
      rowDecoder ∅ (canonicalRow ∅ (.of false))
    simp [rowDecoder, recutRow, canonicalRow, literalRow]
    decide

def commonSuffix_decoder_correct_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.commonSuffix_decoder_correct)
    (Realization decoderSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.commonSuffix_decoder_correct
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.decoderProof
  realizationSource := none
  generated := false
  arena := .source ⟨decoderArena⟩
  objectArena := .source ⟨decoderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source decoderArena ⟨decoderProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize decoderSignature
    (fun _ p u => rowDecoder p.2.1 (canonicalRow p.1 u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms decoderProof
#print axioms commonSuffix_decoder_correct_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
