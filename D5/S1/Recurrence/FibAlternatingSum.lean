/- GID: D5/S1/Recurrence/FibAlternatingSum
   generality: G
   mirror-B: D5/B/S1/Recurrence/FibAlternatingSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The parity-descending Fibonacci sum equals the next source-indexed Fibonacci number minus one. -/

module
prelude
public import OmegaMath.Arithmetic.Fibonacci.AlternatingSum

noncomputable section
@[expose] public section

namespace D5.S1.Recurrence.FibAlternatingSum

open Omega

/-- The source convention `F₀ = F₁ = 1`, so `F k = fib (k + 1)`. -/
def srcFib (k : Nat) : Int := Arithmetic.Fibonacci.shiftedFib k

/-- `F_k + F_{k-2} + ...`; the zero case is empty because the source lemma starts at `k = 1`. -/
def alternatingFibSum (k : Nat) : Int := Arithmetic.Fibonacci.alternatingSum k

theorem alternating_fibonacci_sum (k : Nat) :
    Eq (alternatingFibSum k) ((srcFib k.succ).sub Int.one) :=
  Arithmetic.Fibonacci.alternating_sum_eq k

end D5.S1.Recurrence.FibAlternatingSum
