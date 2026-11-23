# A Cayley code preserving targets

## Abstract

Cutting the cyclic vertices at an anchor transforms a target function into a rooted tree without changing its target multiset.

**Theorem 1.1 (The code preserves every target).**

$$\forall (V: Type), [\operatorname{Finite}\left(V\right)] \forall (a: V), \forall (f: \operatorname{Away}\left(V, a\right) \to V), \forall (i: \operatorname{Away}\left(V, a\right)), \operatorname{parent}\left(\operatorname{snd}\left(\operatorname{rootedCode}\left(a\right)\left(f\right)\right), \operatorname{fst}\left(\operatorname{rootedCode}\left(a\right)\left(f\right)\right), \operatorname{codeCoordinates}\left(a, f\right)\left(i\right)\right) = f\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The code sends a function on the vertices other than the anchor to a rooted tree. It retains the arcs outside the cyclic core and replaces the core cycles by an anchor-first path to the root. A coordinate equivalence matches the original domain to the non-root vertices, including when the core is a singleton.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates](RootedCoordinates.md)
