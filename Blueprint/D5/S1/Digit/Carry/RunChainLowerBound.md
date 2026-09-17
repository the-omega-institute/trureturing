# Carry Chains from a Run of Consecutive Indices

## Abstract

A run of consecutive indices admits a carry chain of quadratic length.

Raw digits are finitely supported functions from natural numbers to natural numbers, added pointwise, and single(i, 1) carries one token at index i. A carry step is one of the four replacements of the frozen carry relation, and CarrySteps(k, r, t) is a chain of exactly k such steps from r to t. The sum below carries one token at each of the L consecutive indices from a to a + L - 1, and is the zero digit vector when L is zero. Division is natural-number division, so L * L / 4 is the integer part of L squared over four.

**Theorem 1.1 (A chain of quadratic length exists).**

$$\forall a \in Nat, \forall L \in Nat, \exists t \in RawDigits, CarrySteps\left(L \times L / 4, sum\left(range\left(L\right), \lambda k \mapsto single\left(a + k, 1\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/RunChainLowerBound.exists_carrySteps_consecutive_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every starting index a and every length L there is a digit vector reached from the run of length L by a chain of exactly L * L / 4 carry steps. The chain is constructed rather than merely shown to exist: one merge at the bottom of the run followed by one split for each remaining duplicate carries the run of length L to the run of length L - 2 together with one isolated token, in L - 1 steps, and a strong induction in steps of two composes these blocks. A parity split evaluates the resulting count under natural-number division. This is a lower bound on the attainable chain length; whether L * L / 4 is also the maximum is not proved here.

## References

- Truth anchor: `D5/S1/Digit/Carry/RunChainLowerBound.exists_carrySteps_consecutive_run`
- Dependency: [D5/S1/Digit/Carry/Successor](Successor.md)
