import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
open D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
open D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
abbrev signature : Signature where
  Params := {P : CutSet // CutPrefixFree P} × Source
  State p := LegalValues (canonicalRow p.1.val p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => canonicalRow p.1.val (evaluateRow (extend _ v.val) (canonicalRow p.1.val p.2)))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (v : LegalValues (canonicalRow P u)), R.readout () (⟨P,hP⟩,u) v = canonicalRow P u

theorem bridge : (type_of% (@legal_values_row)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := legal_values_row

/-- On every admitted prefix-free parameter fiber the faithful old-row output
is constant, so this readout cannot supply observational dependence there. -/
theorem invariant_on_legal_fiber (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (v w : LegalValues (canonicalRow P u)) : actual.readout () (⟨P,hP⟩,u) v = actual.readout () (⟨P,hP⟩,u) w :=
  (legal_values_row P hP u v).trans (legal_values_row P hP u w).symm

/-- This faithful invariant-row readout fails the enrolled template's
observational-dependence obligation on its complete legal-state domain. -/
theorem dependence_impossible : ¬ ObservationalDependence signature actual := by
  intro dep
  obtain ⟨p,v,w,ne⟩ := dep ()
  exact ne (invariant_on_legal_fiber p.1.val p.1.property p.2 v w)

#print axioms bridge
#print axioms actual_law
#print axioms invariant_on_legal_fiber
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
