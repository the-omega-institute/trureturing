# Canonical Fibonacci Carry Barrier

## Abstract

Strict conjugate estimates bound how far a high Fibonacci addition can change canonical support.

**Theorem 1.1 (Lower boundary after high addition).**

Lean statement: `D5/S1/Digit/ZeckendorfCarryBarrier.lower_support_carry_barrier`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfCarryBarrier.lower_support_carry_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem lower_support_carry_barrier (P : List ℕ) (m j : ℕ) (hP : P.IsZeckendorfRep) (hm : 4 ≤ m) (hmin : ∀ k ∈ P, m ≤ k) (hj : m - 1 ≤ j) : ∀ k ∈ wdigits ((P.map Nat.fib).sum + Nat.fib j), m - 2 ≤ k`.

If P is canonical, m is at least four, every index of P is at least m, and j is at least m minus one, then every index in the canonical support of the sum of P and F_j is at least m minus two. Empty supports and the boundary index are included. Strict finite tails and the open conjugate interval of length one identify the normalized error; least-digit dominance gives the support bound.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfCarryBarrier.lower_support_carry_barrier`
- Dependency: [D5/S1/Words/ZeckendorfBeattyBridge](../Words/ZeckendorfBeattyBridge.md)
