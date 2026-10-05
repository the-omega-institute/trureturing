/- GID: D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Merged nonleaf peeling characterizes actual coarse endpoint controllers. -/

import D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CoarseEndpointPeeling

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable shared_history_obstruction)
open ActualCoarseReadoutCompletion (compileRaw encodeHistory cachedExecute completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute fiber)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)

local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "RH" => Hist (fun _ : Address => Reply)
local notation "read" => fun {m : Nat} (F : Fin m → Source) (q : Address) (i : Fin m) =>
  leafLabel (F i) q

/-- Keep the target in the survivor set. Branch and absent form one group,
whose cardinality is at most one at every target-leaf request. -/
noncomputable def Peels {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Prop
  | S, [] => S ⊆ {z}
  | S, q :: qs => q ∈ leaves (F z) ∧
      (fiber (read F) S q none).card ≤ 1 ∧
      Peels F z (fiber (read F) S q (leafLabel (F z) q)) qs

/-- The finite coarse route stops at its first reply different from the target. -/
def peelRoute {m : Nat} (F : Fin m → Source) (z : Fin m) :
    List Address → PassiveProtocol Address (fun _ => Option Bool)
  | [] => .stop
  | q :: qs => .query q (fun y =>
      if y = leafLabel (F z) q then peelRoute F z qs else .stop)

/-- Decode a reached nonleaf singleton or the target at the end of the route.
Malformed or non-singleton replies select the existing acquisition fallback. -/
noncomputable def peelDecode {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → CH → Option (Fin m)
  | _, [], _ => some z
  | S, q :: qs, a :: h =>
      if a.1 = q then
        if a.2 = leafLabel (F z) q then
          peelDecode F z (fiber (read F) S q a.2) qs h
        else if unique : ∃ i, fiber (read F) S q a.2 = {i} then
          some (Classical.choose unique)
        else none
      else none
  | _, _ :: _, [] => none


end D5.S3.Arith.FibonacciAtomic.CoarseEndpointPeeling
