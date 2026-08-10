# Trace Invariance Under Conjugation

## Abstract

The golden trace is invariant under Galois conjugation.

**Theorem 1.1 (Trace invariance).**

$$\operatorname{trace}\left(\operatorname{conj}\left(x\right)\right) = \operatorname{trace}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/TraceConjugation.trace_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating a golden integer preserves its integral trace. In coordinates, conjugation sends `(a,b)` to `(a+b,-b)`, and both traces simplify to `2a+b`.

## References

- Truth anchor: `D5/S0/Carrier/TraceConjugation.trace_conj`
- Dependency: [D5/S0/Carrier/Conj](Conj.md)
