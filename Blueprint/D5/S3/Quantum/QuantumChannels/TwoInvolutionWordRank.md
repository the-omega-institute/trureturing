# Two involutions and homogeneous word rank

## Abstract

Homogeneous operator words in two involutions with a four-dimensional relative-product space.

**Theorem 1.1 (Exact rank at every length).**

$$\forall A \in \operatorname{FiniteDimensionalComplexAlgebra}\left(\right), u \in A, v \in A, n \in \mathbb{N},\; \left(\left(u \cdot u = 1 \land v \cdot v = 1\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{C}, \operatorname{firstFourPowers}\left(u \cdot v\right)\right) \land \left(\left(\forall x \in A,\; x \in \operatorname{powerSpace}\left(u, v\right) \Rightarrow u \cdot v \cdot x \in \operatorname{powerSpace}\left(u, v\right)\right) \land \left(\forall x \in A,\; x \in \operatorname{powerSpace}\left(u, v\right) \Rightarrow v \cdot u \cdot x \in \operatorname{powerSpace}\left(u, v\right)\right)\right)\right)\right) \Rightarrow \operatorname{finrank}\left(\mathbb{C}, \operatorname{wordSpace}\left(u, v, n\right)\right) = \operatorname{min}\left(n + 1, 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.homogeneous_word_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is a finite-dimensional complex algebra, with no commutativity assumption. Products(u,v,0) is {1}; Products(u,v,n+1) consists of u and v multiplied on the left of every exact length-n product. W is its complex linear span. P is the span of 1, uv, (uv)^2 and (uv)^3. The two closure hypotheses are left multiplication by uv and vu on every member of P.

The proof places even and odd word spaces in P and uP. Invertible multiplication exhibits one, two, three and four independent words at lengths zero through three. Rank monotonicity and the invariant space give every later length. This theorem concerns terminal operator spans and supplies no measured history, physical implementation or independent coherent archive.

**Theorem 1.2 (Nonzero generator scaling).**

$$\forall A \in \operatorname{FiniteDimensionalComplexAlgebra}\left(\right), u \in A, v \in A, z \in \mathbb{C}, w \in \mathbb{C}, n \in \mathbb{N},\; \left(z \ne 0 \land w \ne 0\right) \Rightarrow \operatorname{wordSpace}\left(\operatorname{smul}\left(z, u\right), \operatorname{smul}\left(w, v\right), n\right) = \operatorname{wordSpace}\left(u, v, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent nonzero complex weights preserve each homogeneous span. The lifted balanced five-mode theorem consumes this auxiliary result in its live proof.

**Theorem 1.3 (Exact algebra transport).**

$$\forall A \in \operatorname{FiniteDimensionalComplexAlgebra}\left(\right), E \in \operatorname{ComplexAlgebra}\left(\right), f \in \operatorname{AlgHom}\left(\mathbb{C}, A, E\right), u \in A, v \in A, n \in \mathbb{N},\; \operatorname{wordSpace}\left(\operatorname{apply}\left(f, u\right), \operatorname{apply}\left(f, v\right), n\right) = \operatorname{map}\left(\operatorname{wordSpace}\left(u, v, n\right), \operatorname{toLinearMap}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unital complex algebra homomorphism maps the entire exact-length product set, including the empty product. The lifted balanced five-mode theorem consumes this auxiliary equality; injectivity is needed there to preserve dimension.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.homogeneous_word_rank`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_map`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_scale`
