# Rigidity of Torus Generators

## Abstract

A continuous family of torus points with the same actual power-orbit closure is constant on every preconnected parameter subset.

**Theorem 1.1 (A common orbit closure forces constancy).**

$$\forall P \in \operatorname{TopologicalSpaces}\left(\right),\; \forall I \in \operatorname{Types}\left(\right),\; \forall S \in \operatorname{Subsets}\left(P\right),\; \forall g \in P\Rightarrow\operatorname{Circle}\left(\right)^{I},\; \forall G \in \operatorname{Subsets}\left(\operatorname{Circle}\left(\right)^{I}\right),\; \operatorname{IsPreconnected}\left(S\right) \land \left(\operatorname{ContinuousOn}\left(g, S\right) \land \left(\forall p \in S,\; \operatorname{closure}\left(\operatorname{range}\left(n\mapsto\operatorname{g}\left(p\right)^{n}, \operatorname{NaturalNumbers}\left(\right)\right)\right) = G\right)\right)\Rightarrow\forall p \in S,\; \forall q \in S,\; \operatorname{g}\left(p\right) = \operatorname{g}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/TorusGeneratorRigidity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be any topological space, I any index type, S a preconnected subset of P, and g a function from P to the product of circles indexed by I. Assume that g is continuous on S. If the closure of the actual set of nonnegative integer powers of g(p) is one fixed set G for every p in S, then g(p) equals g(q) for every p and q in S.

No finiteness or nonemptiness of I is required. The statement includes empty S, empty parameter spaces, and the empty product. G need not be specified as a subgroup or assumed connected. In particular, finite, proper, and disconnected compact orbit subgroups are all included.

For each circle coordinate, if one value has finite order, its finite set of powers is closed. The common orbit closure places every other coordinate value in this same finite set, so preconnectedness forces constancy. Otherwise all coordinate values have infinite order. The circle is identified with the additive circle of period one, and its representative in the interval [0,1) is continuous because the family avoids the identity. Every representative is irrational. Two distinct values would force a rational intermediate value, a contradiction. Coordinate equality gives equality in the product.

Taking S to be the whole connected parameter space gives constancy of the family. Taking S to be any connected component gives componentwise constancy on an arbitrary parameter space. The finite-power, quotient-circle, and intermediate-value steps use the corresponding Mathlib results. The common-closure hypothesis is essential: the family exp(it) on the real line is continuous and nonconstant.

## References

- Truth anchor: `D5/S3/Fourier/TorusGeneratorRigidity.result`
