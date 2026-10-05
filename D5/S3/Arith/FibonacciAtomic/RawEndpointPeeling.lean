/- GID: D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RawEndpointPeeling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Leaf peeling and actual raw controllers for nested-compensation endpoint costs. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation
import Mathlib.Data.Finset.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore (Controller controllerPolicy controllerOutcome verifyController
  survivors Recipe gain representative phase_foundation)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel Nonconflict seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- The target is retained in the survivor set. Each query is a target leaf,
and its two distinct nonleaf reply groups have at most one member each. -/
def Peels {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Prop
  | S, [] => S ⊆ {z}
  | S, q :: qs => q ∈ leaves (F z) ∧
      (survivors S (vector F q) .branch).card ≤ 1 ∧
      (survivors S (vector F q) .absent).card ≤ 1 ∧
      Peels F z (survivors S (vector F q) (readout q (F z))) qs

/-- Follow the target reply until the first different reply. A singleton
response group selects its complete verifier; other replies start acquisition. -/
noncomputable def peelController {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Controller
  | _, [] => verifyController (F z) (leaves (F z))
  | S, q :: qs => .query q (fun y =>
      if y = readout q (F z) then
        peelController F z (survivors S (vector F q) y) qs
      else if h : ∃ i, survivors S (vector F q) y = {i} then
        verifyController (F (Classical.choose h)) (leaves (F (Classical.choose h)))
      else .fallback)

end D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
