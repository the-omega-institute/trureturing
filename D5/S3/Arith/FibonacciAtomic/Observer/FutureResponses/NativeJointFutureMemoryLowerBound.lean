/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Any finite surjective memory preserving all native future replies has at least eleven states. -/

import D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureClasses
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.Observer.NativeJointFutureClasses

/-!
The memory carrier is allowed to retain distinctions that the future task does
not need.  The theorem only assumes that it is finite, surjective on the
source, and that its readout reconstructs every future reply.  It therefore
counts memory states rather than source representatives.
-/

theorem native_joint_future_memory_lower_bound
    {W : Type*} [Fintype W]
    (memory : Source → W)
    (memory_surjective : Function.Surjective memory)
    (memoryReadout : W → ℕ → Reply × Reply)
    (future_factor : ∀ u k,
      futureReplies u k = memoryReadout (memory u) k) :
    11 ≤ Fintype.card W := by
  have hclassification := native_joint_future_classification
  have hjoint_surjective : Function.Surjective jointClass := hclassification.2.1
  have hjoint_card : Fintype.card JointClass = 11 := hclassification.2.2
  let representative : W → Source := fun w =>
    Classical.choose (memory_surjective w)
  have representative_memory : ∀ w, memory (representative w) = w := by
    intro w
    exact Classical.choose_spec (memory_surjective w)
  let factor : W → JointClass := fun w => jointClass (representative w)
  have factor_surjective : Function.Surjective factor := by
    intro c
    rcases hjoint_surjective c with ⟨u, hu⟩
    refine ⟨memory u, ?_⟩
    have hfuture : ∀ k, futureReplies (representative (memory u)) k =
        futureReplies u k := by
      intro k
      calc
        futureReplies (representative (memory u)) k =
            memoryReadout (memory (representative (memory u))) k :=
          future_factor _ _
        _ = memoryReadout (memory u) k := by
          rw [representative_memory]
        _ = futureReplies u k := (future_factor u k).symm
    have hclass : jointClass (representative (memory u)) = jointClass u :=
      hclassification.1 _ _ |>.mp hfuture
    exact hclass.trans hu
  have hcard : Fintype.card JointClass ≤ Fintype.card W :=
    Fintype.card_le_of_surjective factor factor_surjective
  exact hjoint_card ▸ hcard

#print axioms native_joint_future_memory_lower_bound

end D5.S3.Arith.FibonacciAtomic.Observer.FutureResponses.NativeJointFutureMemoryLowerBound
