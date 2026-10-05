# Tree Parity Kernels

## Abstract

A complete gap parity record preserves the total variation between the actual and reference tree laws.

**Definition 1.1 (Shapes and complete gaps).**

$$\operatorname{Fiber}\left(a, b\right) \sim \operatorname{Shapes}\left(n - 1\right) \times \operatorname{WeakCompositions}\left(d, M\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.intervals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural a and b with a+b>=1, set n=a+b, k=min(a,b), M=max(a,b), and d=k+1. An actual ordered binary tree separates into its ordered shape and the complete gaps between its minority leaves. If a<=b, alpha leaves are the separators; otherwise beta leaves are the separators. The first and last gaps are included. The d nonnegative gap sizes sum to M. The leaf-position subset corresponds to a positive composition of n+1 into d blocks; subtracting one from every block gives the gap sizes. Adding one reverses this operation. All ordered shapes with n-1 internal nodes are retained.

**Definition 1.2 (Complete gap parity record).**

$$\operatorname{xi}\left(t, i\right) = \operatorname{decide}\left(\operatorname{mod}\left(r_{i}, 2\right) = 1\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.gapParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean vector has one coordinate for every gap, including both outside gaps. Its occupied-coordinate count h is the sum of the Boolean digits, and h mod 2 equals M mod 2.

**Definition 1.3 (Reference tree mass).**

$$\operatorname{V}\left(t\right) = \frac{\operatorname{Q}\left(d, M, \operatorname{xi}\left(t\right)\right)}{\operatorname{catalan}\left(n - 1\right) \cdot \operatorname{choose}\left(\frac{M - h}{2} + d - 1, d - 1\right)}$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.referenceTreeMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual tree law U is the uniform mass on Fiber(a,b). The reference mass uses the conditioned Bernoulli parity law Q and the actual uniform conditional law given the complete gap parity. For a legal parity vector, the denominator is the number of actual trees with that record: catalan(n-1) times choose((M-h)/2+d-1,d-1). The parity vector of an actual tree is always legal.

**Theorem 1.4 (Equal distance and two-sided event bounds).**

$$\forall a,b \in \mathbb{N}, ((1 \leq a + b) \land (d \leq M)) \Rightarrow (\operatorname{pushforward}\left(xi, U\right) = \operatorname{R}\left(d, M\right)) \land ((\forall t, 0 \leq \operatorname{V}\left(t\right)) \land ((\sum_{t} \operatorname{V}\left(t\right) = 1) \land ((\operatorname{pushforward}\left(xi, V\right) = \operatorname{Q}\left(d, M\right)) \land ((\operatorname{totalVariation}\left(U, V\right) = \operatorname{totalVariation}\left(\operatorname{R}\left(d, M\right), \operatorname{Q}\left(d, M\right)\right)) \land ((((2 \leq d) \land (3 \cdot d \leq M)) \Rightarrow \forall A, (\operatorname{max}\left(0, \operatorname{V}\left(A\right) - epsilon\right) \leq \operatorname{U}\left(A\right)) \land (\operatorname{U}\left(A\right) \leq \operatorname{min}\left(1, \operatorname{V}\left(A\right) + epsilon\right))) \land (d = 1 \Rightarrow U = V))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/TreeParityKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural composition a,b with a+b>=1 and M>=d, the parity pushforward of U equals R(d,M). The reference mass is nonnegative, sums to one, and its parity pushforward equals Q(d,M). The total variation of the two tree laws equals that of R and Q. When d>=2 and M>=3d, every event A in the actual composition fiber satisfies max(0,V(A)-epsilon)<=U(A)<=min(1,V(A)+epsilon), where epsilon=min(1,5(sqrt(d)/M+d(d-1)/M^2)). For d=1 the actual and reference tree laws coincide. The shape-gap equivalence reduces parity-fiber counting to the coordinatewise bijection r_i=2t_i+xi_i. The resulting fiber count normalizes a common uniform conditional kernel. Summing the absolute mass difference within each fiber gives the exact distance identity. The finite parity bound and the event characterization of total variation give both event inequalities.

## References

- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.gapParity`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.intervals`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.referenceTreeMass`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](../Arith/FibonacciAtomic/GenealogicalFiberTransport.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration](../Combinatorics/Geometry/CrownOrderPolytopeEnumeration.md)
- Dependency: [D5/S3/TotalVariation/ParityCompositionKernel](ParityCompositionKernel.md)
