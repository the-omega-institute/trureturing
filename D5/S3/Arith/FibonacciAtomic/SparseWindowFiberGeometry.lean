/- GID: D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse window arc fibres are connected components of the circle away from their translated cuts. -/

import D5.S1.Digit.Infinite.SparseWindowMutualDetermination
import D5.S1.Phase.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SparseWindowFiberGeometry

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.WindowCylinderPartition
open D5.S1.Digit.Infinite.SparseWindowMutualDetermination
open D5.S1.Phase
open Set

/-- The points giving the specified window label at every retained time. -/
noncomputable def fiber (m : ℕ) (S : Finset ℕ) (p : (t : S) → X m) : Set Circle :=
  {z | ∀ t : S, z + goldenPhase (t.val : ℤ) ∈ A (p t)}

/-- The circle with all translated window cuts removed. -/
noncomputable def regularDomain (m : ℕ) (S : Finset ℕ) : Set Circle :=
  (E '' (↑(cuts m S) : Set ℕ))ᶜ

end D5.S3.Arith.FibonacciAtomic.SparseWindowFiberGeometry
