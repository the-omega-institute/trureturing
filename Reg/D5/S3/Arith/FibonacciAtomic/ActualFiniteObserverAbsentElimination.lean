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
  Params := RawHistory × Address
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
    ∀ q : Address, R.readout () (cache, q) U = readout q U

theorem bridge : (type_of% (@queryReply_eq_readout)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := queryReply_eq_readout

#print axioms bridge
#print axioms actual_law
end Reg.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
