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
end Reg.D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
