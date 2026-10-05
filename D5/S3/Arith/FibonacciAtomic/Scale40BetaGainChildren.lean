/- GID: D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual leaf reports fix beta resources in literal Fibonacci blocks. -/

import D5.S3.Arith.FibonacciAtomic.ActualStrictHistoryCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale40BetaGainChildren

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout Positive)
open ActualImageSevenLeafSeparation (thirdImage E A C Nonconflict leafAddresses leafLabel)
open ActualLeafHistoryRigidity
open ActualStrictHistoryCapacity (queue reports)
open ActualJointResponseCostCore (Recipe routeTrace)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)

/-- The actual beta frontier, using the existing native leaf-address enumeration. -/
def betaLeaves (P : Source) : Finset Address :=
  (leafAddresses P).filter fun u => readout u P = .beta

/-- Only the five-row decoder's actual leaf reports contribute fixed beta addresses. -/
def psi (H : Hist (fun _ : Address => Reply)) : Finset Address :=
  (forcedBlocks (reports H)).biUnion fun b =>
    (betaLeaves b.2.tree).image (b.1 ++ ·)

end D5.S3.Arith.FibonacciAtomic.Scale40BetaGainChildren
