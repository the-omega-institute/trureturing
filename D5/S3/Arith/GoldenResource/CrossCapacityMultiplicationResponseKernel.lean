/- GID: D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All multiplication responses across capacity boxes are classified by remaining capacities, squarefreeness, and parity. -/

import D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.CrossCapacityMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths
open D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Two states in possibly different capacity boxes agree on all multiplication words. -/
def EqPlusAll (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) : Prop :=
  (Setoid.ker (plusAllObservation (P := P))).r ⟨A, a⟩ ⟨B, b⟩

end D5.S3.Arith.GoldenResource.CrossCapacityMultiplicationResponseKernel
