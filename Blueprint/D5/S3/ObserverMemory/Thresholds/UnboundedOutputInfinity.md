# Unbounded Output Infinity

## Abstract

An unbounded natural-valued output forces its carrier to be infinite.

**Theorem 1.1 (Unbounded output forces an infinite carrier).**

$$\forall \alpha, f: \alpha \to \mathbb{N},\ (\forall B: \mathbb{N}, \exists x: \alpha, B < f(x)) \Rightarrow \operatorname{Infinite}(\alpha).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Thresholds/UnboundedOutputInfinity.unbounded_output_implies_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be any carrier and let f assign a natural-number output to each object. If every natural bound is strictly exceeded by some output, then alpha is infinite.

If alpha were finite, Mathlib's Finite.bddAbove_range would supply an upper bound for the range of f. Applying the hypothesis to that bound gives an immediate contradiction.

This closes only the unbounded-output-implies-infinite-object clause of the source atom. Its entropy, quantum-tax, zeta, and continued-fraction assertions are not claimed here.

## References

- Truth anchor: `D5/S3/ObserverMemory/Thresholds/UnboundedOutputInfinity.unbounded_output_implies_infinite`
