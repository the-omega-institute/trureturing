# Golden Eigenpair and Fibonacci Residual

## Abstract

Forward-shift iteration exposes both golden coordinates and the exact Fibonacci contracting residual.

**Theorem 1.1 (The shifted weight has two golden faces).**

$$\begin{aligned}\forall k: \mathbb{N},\\(\langle\operatorname{iterate}\left(shift, k, expandingSequence\right)\left(0\right), \operatorname{iterate}\left(shift, k, contractingSequence\right)\left(0\right)\rangle = \langle\varphi^{k+1}, \psi^{k+1}\rangle) \land\\(fibonacciWeight\left(k+1\right) - \varphi \cdot fibonacciWeight\left(k\right) = \psi^{k+1}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/GoldenEigenpairResidual.golden_eigenpair_and_fibonacci_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source pair is constructed by iterating the canonical forward shift on the two frozen golden eigensequences and evaluating both at index zero. Induction applies the frozen one-step eigenvector laws, so the two coordinates are the displayed powers.

The second conjunct directly applies the frozen Fibonacci residual theorem. Subtracting the expanding multiple of the current weight from the next weight leaves the contracting golden coordinate exactly.

No new sequence or weight is defined by the target equation; the public objects are the existing shift, eigensequences, and Fibonacci weight.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/GoldenEigenpairResidual.golden_eigenpair_and_fibonacci_residual`
- Dependency: [D5/S1/Recurrence/BilateralLiftUniqueness](../BilateralLiftUniqueness.md)
