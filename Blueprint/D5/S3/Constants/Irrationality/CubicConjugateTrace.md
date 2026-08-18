# Conjugate Trace

## Abstract

The two non-Perron roots sum to one minus the base, which is irrational.

The three roots of the cubic sum to one, an integer. Splitting off the Perron factor leaves a quadratic whose linear coefficient reads off the sum of the other two roots: one minus the base. That number is irrational, so the expanding root does not sit in a rational trace relation with the contracting pair.

This is what separates the cubic from the quadratic case. There the two roots are the whole conjugate set and their sum is an integer; here the dominant root alone carries no such relation, and the integrality that the quadratic tower enjoys is a privilege of having exactly two faces.

**Theorem 1.1 (The Perron root does not carry the trace).**

$$\operatorname{Irrational}\left(1 - \mathit{tribonacciConstant}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/CubicConjugateTrace.cubic_trace_is_not_carried_by_the_perron_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorisation was already in the tree; the sum of roots was not, and neither was the irrationality of the base, which landed separately in the same session. Without it this conclusion has no proof, which is how an unproved obvious fact blocks a whole downstream line rather than a single lemma.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/CubicConjugateTrace.cubic_trace_is_not_carried_by_the_perron_root`
- Dependency: [D5/S0/Tower/Tribonacci/Binet](../../../S0/Tower/Tribonacci/Binet.md)
- Dependency: [D5/S3/Constants/Irrationality/TribonacciIrrationality](TribonacciIrrationality.md)
