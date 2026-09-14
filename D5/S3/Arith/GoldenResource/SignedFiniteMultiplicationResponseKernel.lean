/- GID: D5/S3/Arith/GoldenResource/SignedFiniteMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/SignedFiniteMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite multiplication and division responses classify states by squarefree distance and truncated two-sided guards. -/

import D5.S3.Arith.GoldenResource.CrossCapacityMultiplicationResponseKernel

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.SignedFiniteMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths
open D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The defect counts the divisions needed to make every coordinate at most one. -/
def defect (a : P → ℕ) : ℕ := ∑ p, (a p - 1)

/-- The guard code records both distances to each coordinate boundary up to the horizon. -/
def guardCode (A a : P → ℕ) (h : ℕ) : P → ℕ × ℕ :=
  fun p => (min (a p) h, min (A p - a p) h)

/-- A signed observation records responses to all multiplication and division words within its horizon. -/
def signedObservation (h : ℕ) (x : Located P) :
    {w : List (Instruction P) // w.length ≤ h} → Option ℤ :=
  fun w => response x w.val

/-- Two states agree when all signed responses within the finite horizon agree. -/
def EqSigned (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) (h : ℕ) : Prop :=
  (Setoid.ker (signedObservation (P := P) h)).r ⟨A, a⟩ ⟨B, b⟩

end D5.S3.Arith.GoldenResource.SignedFiniteMultiplicationResponseKernel
