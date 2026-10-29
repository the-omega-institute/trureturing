/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSourceParallelRefutation
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSourceParallelRefutation.claim; result=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSourceParallelRefutation.result; claim=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSourceParallelRefutation.claim
   digest: Repeated original source shifts by three and four admit no natural block ranks. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositivePotentialCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceParallelRefutation
open NativePositiveBranchReduction NativePositiveImageCover NativePositivePotentialCover
open NativeTermUnification

/-- The original comparisons U=V+3, U=V+3, U=V+4, with repetitions retained. -/
def branchInput : List (BranchEquation Bool) :=
  [.shift true 3 false, .shift true 3 false, .shift true 4 false]

/-- Both names have the same single residual sort after shape identification. -/
def sourceTerms : Bool → Term Bool := fun _ => .of (.inr false)

/-- Feasibility of the actual natural rank equations on a one-leaf shape. -/
def claim : Prop := ∃ u : NativePositiveImageCover.Occurrence Bool → Unit → Nat,
  BlockSolution branchInput sourceTerms false u

/-- The finite checker rejects the repeated parallel source comparisons;
its closed-walk correctness then excludes every natural rank assignment. -/
theorem result : ¬ claim := by
  have rejected : checkSourceConsistency branchInput sourceTerms false = false := by decide
  rintro ⟨u, hu⟩
  have cycles : ZeroCycles branchInput sourceTerms false :=
    (zeroCycles_iff branchInput sourceTerms false).mpr
      ⟨fun v => (u v () : Int), fun e he => hu e he ()⟩
  have accepted := (source_consistency_iff branchInput sourceTerms false).mpr cycles
  rw [rejected] at accepted
  cases accepted

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceParallelRefutation
