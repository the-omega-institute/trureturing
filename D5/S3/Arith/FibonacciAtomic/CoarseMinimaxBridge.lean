/- GID: D5/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Constant-query pruning yields a coarse endpoint and the universal two-excess lower bound. -/

import D5.S3.Arith.FibonacciAtomic.CoarseEndpointSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CoarseMinimaxBridge

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves Strategy cost paid terminal Positive)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict seven_leaf_separation)
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable shared_history_obstruction)
open CoarseEndpointPeeling (Peels)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute fiber)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "RH" => Hist (fun _ : Address => Reply)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "read" => fun {m : Nat} (F : Fin m → Source) (q : Address) (i : Fin m) =>
  leafLabel (F i) q

end D5.S3.Arith.FibonacciAtomic.CoarseMinimaxBridge
