# Golden-Coordinate Recursive Tail Structure

## Abstract

Golden floor coordinates have the two local fiber shapes needed to recurse across a fixed negative base-phi tail.

**Theorem 1.1 (Below the inverse-golden cut a coordinate fiber has three consecutive values).**

$$0<T<\varphi^{-1} \Rightarrow \{v : B(v)=B\}=\{s,s+1,s+2\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Beatty-floor coordinate of the nonnegative half is constant on exactly three consecutive natural coordinates when the fixed negative-tail value lies strictly below the inverse-golden cut.

**Theorem 1.2 (Above the inverse-golden cut a coordinate fiber has two consecutive values).**

$$\varphi^{-1}\leq T<1 \Rightarrow \{v : B(v)=B\}=\{s,s+1\}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At or above the inverse-golden cut the same floor fiber contains exactly two consecutive coordinates. The canonical seam condition removes the second coordinate when the first negative digit is one.

Together these two floor classifications are the cropped recursive structure needed for complete negative-tail fibers. They do not formalize all word appendants or the conjectural finite-prefix classification in Dekking's paper.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_large`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiRecursiveStructure.positiveCoordinate_fiber_small`
- Dependency: [D5/S1/Words/Expansions/BasePhiTailBounds](BasePhiTailBounds.md)
- Dependency: [D5/S1/Words/ZeckendorfBeattyBridge](../ZeckendorfBeattyBridge.md)
