import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)

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

abbrev supportSignature : Signature where
  Params := CutSet × Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Address
  Anchor := Empty
  finiteAnchor := inferInstance

def supportActual : Realization supportSignature := realize supportSignature
  (fun _ p u => exteriorHoles p.2 (cutExterior p.1 p.2 u)) (fun e => nomatch e)
def supportBad : Realization supportSignature := realize supportSignature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev supportArena : Arena where
  signature := supportSignature
  Law R := ∀ (P : CutSet) (a : Address) (t : Source), R.readout () (P,a) t = reachedHoles P a t

private theorem support_bad : ¬ supportArena.Law supportBad := by
  intro h
  have eq := h {[]} [] (.of true)
  simpa [supportBad,realize,reachedHoles] using eq

def supportProof : Registration supportArena (type_of% (@exteriorHoles_cut)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨exteriorHoles_cut,supportBad,support_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,support_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨({[false]},[]),.of true,.mul (.of true) (.of true),?_⟩
    change exteriorHoles [] (cutExterior {[false]} [] (.of true)) ≠
      exteriorHoles [] (cutExterior {[false]} [] (.mul (.of true) (.of true)))
    rw [exteriorHoles_cut,exteriorHoles_cut]
    simp [reachedHoles]

noncomputable def exteriorHoles_cut_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.exteriorHoles_cut)
    (Realization supportSignature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.exteriorHoles_cut
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.supportProof
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ p u => exteriorHoles p.2 (cutExterior p.1 p.2 u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms supportProof
#print axioms exteriorHoles_cut_registration

open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)

abbrev namingSignature : Signature where
  Params := Σ _ : CutSet, Σ _ : Source, Σ _ : Address → Nat, Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def namingActual : Realization namingSignature := realize namingSignature
  (fun _ p t => nameExterior p.2.2.1 (cutExterior p.1 p.2.2.2 t)) (fun e => nomatch e)

def namingBad : Realization namingSignature := realize namingSignature
  (fun _ _ _ => .of (.inl false)) (fun e => nomatch e)

abbrev namingArena : Arena where
  signature := namingSignature
  Law R := ∀ (P : CutSet) (_ : CutPrefixFree P) (root : Source)
    (names : Address → Nat),
    (∀ p ∈ orderedHoles P root, names p = classOrdinal P root p) →
    ∀ (a : Address) (t : Source), subtree a root = some t →
    R.readout () ⟨P,⟨root,⟨names,a⟩⟩⟩ t = literalRow P root a t

private theorem naming_bad_law : ¬ namingArena.Law namingBad := by
  intro law
  have bad := law ∅ empty_prefixFree (.of true) (fun _ => 0)
    (by simp [orderedHoles,reachedHoles]) [] (.of true) rfl
  change (FreeMagma.of (.inl false) : LiteralRow) = .of (.inl true) at bad
  cases bad

def namingProof : Registration namingArena (type_of% (@nameExterior_correct)) where
  actual := namingActual
  bridge := Iff.rfl
  variation := ⟨@nameExterior_correct,namingBad,naming_bad_law⟩
  sensitivity := ⟨fun i => ⟨namingBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,naming_bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨∅,⟨.of true,⟨fun _ => 0,[]⟩⟩⟩,.of true,.of false,?_⟩
    simp [namingActual,realize,nameExterior,cutExterior]
    decide

noncomputable def nameExterior_correct_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.nameExterior_correct)
    (Realization namingSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.nameExterior_correct
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.namingProof
  realizationSource := none
  generated := false
  arena := .source ⟨namingArena⟩
  objectArena := .source ⟨namingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source namingArena ⟨namingProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize namingSignature namingActual.readout namingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
    definition := none
    coordinates := #[0,2,3,5]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","fn","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms namingProof
#print axioms nameExterior_correct_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
