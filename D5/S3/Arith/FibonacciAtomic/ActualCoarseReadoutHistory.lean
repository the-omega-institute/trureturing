/- GID: D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fresh coarse divergence and saturated common-history obstruction. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import Mathlib.Data.List.Infix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (leafLabel leafAddresses Nonconflict)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- The leaf labels remain distinct; branch and absent have the same coarse reply. -/
def κ : Reply → Option Bool
  | .alpha => some true
  | .beta => some false
  | .branch | .absent => none

/-- Coarsening retains every actual address, its order, and repeated requests. -/
def κHist (h : Hist (fun _ : Address => Reply)) : Hist (fun _ : Address => Option Bool) :=
  h.map (fun a => ⟨a.1, κ a.2⟩)

/-- The original selector depends only on its coarse chronological history. -/
def CoarseObservable (p : Policy) : Prop :=
  ∀ h k, κHist h = κHist k → p h = p k

end D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory
