# Pigeonhole Fibers

## Abstract

A reading space of smaller cardinality cannot distinguish every object.

**Theorem 1.1 (A smaller reading space forces a nontrivial fiber).**

$$\operatorname{card}(Readings) < \operatorname{card}(Objects) \Rightarrow \exists x, y \in Objects, x \neq y \land read(x) = read(y)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber` (`✓ std3`). ∎

*Citation.* Peter Winkler (2020). *The Pigeonhole Principle*. DOI: [10.1201/9780429262913-ch12](https://doi.org/10.1201/9780429262913-ch12).

*Commentary.*

For any object type, reading type, and reading map, a strict cardinal inequality from readings to objects rules out injectivity. Therefore two distinct objects have the same reading. The proof is the cardinal form of the pigeonhole principle: an assumed injection would reverse the strict inequality by making the object cardinal no larger than the reading cardinal.

The source atom's finite-reading phrase describes the intended application. Finiteness is not an additional premise of the Lean theorem; the stated strict cardinal inequality alone carries the collision conclusion.

## References

- Truth anchor: `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`
