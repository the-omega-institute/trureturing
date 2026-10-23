import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination (RawHistory)
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (acquisitionTrace)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
abbrev signature : Signature where
  Params := Source
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ h => encodeHistory (kappa_hist h)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Source) (h : RawHistory), h.IsPrefix (acquisitionTrace [] U) → R.readout () U h = h

theorem bridge : (type_of% (@acquisition_prefix_representative)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := acquisition_prefix_representative

#print axioms bridge
#print axioms actual_law

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (.of true) [⟨[], .alpha⟩] (by rfl)
  cases bad

def acquisitionProof : Registration arena (type_of% (@acquisition_prefix_representative)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨.of true, [], [⟨[], .alpha⟩], ?_⟩
    intro bad
    cases bad

#print axioms acquisitionProof




noncomputable def acquisition_prefix_representative_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion.acquisition_prefix_representative) (Realization arena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion.acquisition_prefix_representative
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion.acquisitionProof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨acquisitionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arena.signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms acquisition_prefix_representative_registration

end Reg.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
