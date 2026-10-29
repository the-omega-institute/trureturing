import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSignedObservationExtraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (readout Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery (CutSet CutPrefixFree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern Frontier fill)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation (Record Holds)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber (NegativeRecord)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSignedObservationExtraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSignedObservationExtraction

abbrev Params := CutSet × CutSet × Row × Row × List Record × List NegativeRecord

abbrev signature : Signature where
  Params := Params
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => InputHolds p.1 p.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2 u) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P Q : CutSet) (_ : CutPrefixFree P) (_ : CutPrefixFree Q)
    (old target : Row) (H : List Record) (K : List NegativeRecord) (u : Source),
    R.readout () (P,Q,old,target,H,K) u ↔
      ∃ p : Pattern (requiredDepth P Q H K), ∃ v : Frontier p → Source,
        fill p v = u ∧ ExtractedHolds P Q old target H K
          (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells.patternTerm p id) v

private theorem empty_cut : CutPrefixFree (∅ : CutSet) := by
  intro a ha
  simp at ha

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  let u : Source := .of true
  let row := literalRecord ∅ u
  have yes : InputHolds ∅ ∅ row row [] [] u := by
    exact ⟨rfl, by simp [Holds], by simp, rfl⟩
  have rhs := (entire_input_extraction ∅ ∅ empty_cut empty_cut row row [] [] u).mp yes
  exact (law ∅ ∅ empty_cut empty_cut row row [] [] u).mpr rhs

def proof : Registration arena (type_of% (@entire_input_extraction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entire_input_extraction, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let row := literalRecord ∅ (.of true)
    let H : List Record := [.literal 0 [] .alpha]
    refine ⟨(∅,∅,row,row,H,[]), .of true, .of false, ?_⟩
    intro eq
    change InputHolds ∅ ∅ row row H [] (.of true) =
      InputHolds ∅ ∅ row row H [] (.of false) at eq
    have yes : InputHolds ∅ ∅ row row H [] (.of true) := by
      refine ⟨rfl, ?_, by simp, rfl⟩
      simp [H, Holds, Record.Holds, readout]
    have no := eq ▸ yes
    have literal := no.2.1 (.literal 0 [] .alpha) (by simp [H])
    change Reply.beta = Reply.alpha at literal
    cases literal

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSignedObservationExtraction.entire_input_extraction)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSignedObservationExtraction.entire_input_extraction
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSignedObservationExtraction.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u =>
    InputHolds p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 u)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSignedObservationExtraction
    definition := none
    coordinates := #[0,1,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSignedObservationExtraction
