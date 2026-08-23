# Complete Negative Base-Phi Tail Fibers

## Abstract

Every nonempty complete negative base-phi tail of a positive natural has a singleton or three-consecutive fiber.

**Theorem 1.1 (Complete negative tails have the singleton-trident dichotomy).**

$$d_{-1}=1 \Rightarrow F_N=\{N\},\ d_{-1}=0 \Rightarrow \exists! q,\ F_N=\{q,q+1,q+2\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiTailFiber.negative_tail_fiber_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural whose canonical expansion reaches a negative exponent, the complete negative-position digit tail determines that natural uniquely when its first digit is one. When the first digit is zero, the same tail occurs at exactly three consecutive positive naturals, with a unique least member.

This is the singleton-trident consequence of Dekking's recursive structure used by the frontier theorem. It is deliberately narrower than a formalization of the paper's complete recursive word presentation.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiTailFiber.negative_tail_fiber_shape`
- Dependency: [D5/S1/Words/Expansions/BasePhiRecursiveStructure](BasePhiRecursiveStructure.md)
