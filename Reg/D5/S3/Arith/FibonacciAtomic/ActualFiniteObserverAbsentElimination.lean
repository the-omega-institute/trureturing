import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
abbrev signature : Signature where
  Params := Sigma (fun _ : RawHistory => Address)
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p U => queryReply p.1 p.2 U) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (cache : RawHistory) (U : Source), CacheTruth cache U →
    ∀ q : Address, R.readout () ⟨cache, q⟩ U = readout q U

theorem bridge : (type_of% (@queryReply_eq_readout)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := queryReply_eq_readout

#print axioms bridge
#print axioms actual_law

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .branch) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h [] (.of true) (by simp [CacheTruth]) []
  cases bad

noncomputable def queryProof : Registration arena (type_of% (@queryReply_eq_readout)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨[], []⟩, .of true, .of false, ?_⟩
    intro bad
    cases bad

#print axioms queryProof




noncomputable def queryReply_eq_readout_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.queryReply_eq_readout) (Realization arena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.queryReply_eq_readout
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.queryProof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨queryProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arena.signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
    definition := none
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms queryReply_eq_readout_registration

end Reg.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
