# Native ambient beta cherry sectors

## Abstract

Six actual ambient pair actions imply the exact period and higher-power identities.

**Theorem 1.1 (All six ambient actions).**

$$\forall t: \operatorname{Source}\left(\right), (\forall p: \operatorname{Address}\left(\right), ((\operatorname{subtree}\left(p, t\right) = \operatorname{some}\left(\operatorname{mul}\left(\operatorname{beta}\left(\right), \operatorname{beta}\left(\right)\right)\right)) \Rightarrow ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)\right) = (\operatorname{vector}\left(p, \operatorname{L}\left(\right)\right)) + (\operatorname{vector}\left(p, \operatorname{R}\left(\right)\right))) \land ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{L}\left(\right)\right)\right) = ((\operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)) + (\operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right))) + (\operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right))) \land ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right)\right) = (\operatorname{vector}\left(p, \operatorname{L}\left(\right)\right)) + (\operatorname{vector}\left(p, \operatorname{LLL}\left(\right)\right))) \land ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{LLL}\left(\right)\right)\right) = \operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right)) \land ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{R}\left(\right)\right)\right) = \operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)) \land (\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right)\right) = \operatorname{vector}\left(p, \operatorname{L}\left(\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector.attained_actions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a literal original beta cherry at address p, vector(p,z) is the difference of coordinate vectors at pLz and pRz. The constants empty, L, R, LL, LR and LLL mean the corresponding lists of false and true. B is adjacency of grown(t), computed from its actual material and neighbor lists. Each equality is an equality of fields at every address. A complete local calculation includes the common parent, where the two owner contributions cancel. The zero-root transport theorem carries the calculation through an arbitrary native context, including every exterior coordinate.

**Theorem 1.2 (Period two and exact higher powers).**

$$\forall t: \operatorname{Source}\left(\right), (\forall p: \operatorname{Address}\left(\right), ((\operatorname{subtree}\left(p, t\right) = \operatorname{some}\left(\operatorname{mul}\left(\operatorname{beta}\left(\right), \operatorname{beta}\left(\right)\right)\right)) \Rightarrow ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{half}\left(p\right)\right) = \frac{(\operatorname{vector}\left(p, \operatorname{R}\left(\right)\right)) - (\operatorname{vector}\left(p, \operatorname{LLL}\left(\right)\right))}{2}) \land ((\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{half}\left(p\right)\right)\right) = \operatorname{half}\left(p\right)) \land ((\operatorname{iterate}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), 2, \operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)\right) = ((2 \cdot (\operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right))) + (\operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right))) + (\operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right))) \land ((\operatorname{iterate}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), 2, \operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right)\right) = ((\operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)) + (\operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right))) + (\operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right))) \land (\operatorname{iterate}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), 4, \operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right)\right) = ((6 \cdot (\operatorname{vector}\left(p, \operatorname{empty}\left(\right)\right))) + (5 \cdot (\operatorname{vector}\left(p, \operatorname{LL}\left(\right)\right)))) + (4 \cdot (\operatorname{vector}\left(p, \operatorname{LR}\left(\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector.attained_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write a=vector(p,empty), b=vector(p,L), c=vector(p,LL), d=vector(p,LLL), e=vector(p,R), f=vector(p,LR), and h=(a-c)/2. All scalars are rational. These identities use the six proved native actions and linearity of the actual neighbor sum. The iterate exponents are literal natural numbers; no finite-depth approximation is involved.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector.attained_actions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector.attained_powers`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth](NativeFreshSensorGrowth.md)
