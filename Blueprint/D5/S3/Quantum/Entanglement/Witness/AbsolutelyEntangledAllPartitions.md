# Simultaneous entanglement for all fixed tensor partitions

## Abstract

Every composite dimension admits a finite set with one state entangled for all fixed tensor partitions in each frame.

**Definition 1.1 (Ordered nontrivial factorizations).**

$$\forall \left(d: \mathbb{N}\right), \left(\operatorname{Partition}\left(d\right) = \{\left(p: \Sigma \left(k: \mathbb{N}\right), \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{N}\right)\right) \mid \left(2 \le \left(p\right).1\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(\left(p\right).1\right)\right), \left(2 \le \left(p\right).2\left(i\right)\right)\right) \land \left(\prod_{\left(i: \operatorname{Fin}\left(\left(p\right).1\right)\right)} \left(\left(p\right).2\left(i\right)\right) = d\right)\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.Partition` (`✓ std3`).

*Citation.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

A partition is an ordered list of k natural dimensions, with k at least two, each dimension at least two, and product d. The pair consisting of k and its dimension function is restricted by these three conditions. These are the tensor partitions described in main.tex, line 308 and Definition 3, lines 310–317; factor order is retained.

**Definition 1.2 (The fixed mixed-radix coordinates).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(p: \operatorname{Partition}\left(d\right)\right), \left(\left(\operatorname{partitionEquiv}\left(p\right): \operatorname{Equiv}\left(\left(\left(i: \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).1\right)\right)\right) \to \left(\operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right)\right), \operatorname{Fin}\left(d\right)\right)\right) = \operatorname{Equiv.trans}\left(\operatorname{finPiFinEquiv}, \operatorname{finCongr}\left(\left(\left(\operatorname{Subtype.property}\left(p\right)\right).2\right).2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.partitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

The mixed-radix equivalence first identifies a tuple of local indices with an index below the product of the dimensions, then uses the product equality to identify that index type with Fin d. Thus each ordered factorization has one specified tensor coordinate system. The fixed orthonormal basis in the source's Corollary, main.tex, lines 499–508, motivates fixing these identifications before varying the global unitary.

**Definition 1.3 (Tensor products in the fixed coordinates).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(p: \operatorname{Partition}\left(d\right)\right), \left(\forall \left(\rho: \left(\left(i: \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).1\right)\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right), \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right), \mathbb{C}\right)\right)\right), \left(\operatorname{productState}\left(p, \rho\right) = \operatorname{Matrix.submatrix}\left(\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\lambda \left(i: \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).1\right)\right) \mapsto \left(\operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right)\right), \rho\right), \operatorname{Equiv.toFun}\left(\operatorname{Equiv.symm}\left(\operatorname{partitionEquiv}\left(p\right)\right)\right), \operatorname{Equiv.toFun}\left(\operatorname{Equiv.symm}\left(\operatorname{partitionEquiv}\left(p\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.productState` (`✓ std3`).

*Citation.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

Given one square complex matrix for each factor, take their tensor product and reindex both matrix coordinates by the inverse mixed-radix equivalence. Equivalently, the entry at two global indices is the product of the local matrix entries at their corresponding local indices. This expresses the tensor product of subsystems in Definition 3(i), main.tex, line 314. The construction accepts arbitrary local matrices, without positivity or trace assumptions.

**Definition 1.4 (Full separability for a partition).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(p: \operatorname{Partition}\left(d\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{Separable}\left(p, \rho\right) = \left(\rho \in \operatorname{convexHull}\left(\mathbb{R}, \{\left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \mid \exists \left(\tau: \left(\left(i: \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).1\right)\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right), \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).2\left(i\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(\left(\operatorname{Subtype.val}\left(p\right)\right).1\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\tau\left(i\right)\right)\right) \land \left(\operatorname{Matrix.trace}\left(\tau\left(i\right)\right) = \left(1: \mathbb{C}\right)\right)\right)\right) \land \left(\sigma = \operatorname{productState}\left(p, \tau\right)\right)\right)\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.Separable` (`✓ std3`).

*Citation.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

A matrix is separable for p when it belongs to the real convex hull of tensor products of local positive semidefinite matrices of complex trace one. Thus it is a finite convex combination of local density products. This gives the density-matrix meaning of separability for the tensor partition in Definition 3, main.tex, lines 312–315.

**Definition 1.5 (One common entangled state after each unitary).**

$$\operatorname{claim} = \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \mathbb{N}\right), \left(\forall \left(b: \mathbb{N}\right), \left(\left(2 \le a\right) \Rightarrow \left(\left(2 \le b\right) \Rightarrow \left(\left(d = \left(a\right) \cdot \left(b\right)\right) \Rightarrow \left(\exists \left(s: \operatorname{Finset}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in s\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \land \left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right)\right)\right)\right) \land \left(\forall \left(u: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(u \in \operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \Rightarrow \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in s\right) \land \left(\forall \left(p: \operatorname{Partition}\left(d\right)\right), \left(\neg \left(\operatorname{Separable}\left(p, \left(\left(u\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Star.star}\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

For every factorization d = a times b with a and b at least two, there is one finite set s of positive semidefinite complex matrices of trace one. For every special unitary matrix u, some member of s becomes nonseparable for every partition after conjugation by u. The chosen member can depend on u, but must serve all partitions at once. This is the fixed-coordinate reading of the question in main.tex, line 509, with partitions specified by the mixed-radix identifications above.

**Theorem 1.6 (Positive summands annihilate the orthogonal complement).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\iota: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\iota\right)], \left(\forall \left(w: \left(\iota\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(a: \left(\iota\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(i: \iota\right), \left(\left(0: \mathbb{R}\right) \le w\left(i\right)\right)\right) \Rightarrow \left(\left(\forall \left(i: \iota\right), \left(\operatorname{Matrix.PosSemidef}\left(a\left(i\right)\right)\right)\right) \Rightarrow \left(\forall \left(v: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right), \left(\forall \left(t: \mathbb{R}\right), \left(\left(\sum_{\left(i: \iota\right)} \left(\operatorname{SMul.smul}\left(w\left(i\right), a\left(i\right)\right)\right) = \operatorname{SMul.smul}\left(t, \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(v\right)\right)\right) \Rightarrow \left(\forall \left(j: \iota\right), \left(\left(\left(0: \mathbb{R}\right) < w\left(j\right)\right) \Rightarrow \left(\forall \left(x: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\operatorname{dotProduct}\left(\operatorname{Star.star}\left(v\right), x\right) = \left(0: \mathbb{C}\right)\right) \Rightarrow \left(\operatorname{Matrix.mulVec}\left(a\left(j\right), x\right) = \left(0: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.summand_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positively weighted positive semidefinite summand of a real multiple of a rank-one density annihilates every vector orthogonal to its defining vector.

**Theorem 1.7 (Columns supported on one vector).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(v: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\neg \left(v = \left(0: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right)\right)\right) \Rightarrow \left(\forall \left(a: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.IsHermitian}\left(a\right)\right) \Rightarrow \left(\left(\forall \left(x: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\operatorname{dotProduct}\left(\operatorname{Star.star}\left(v\right), x\right) = \left(0: \mathbb{C}\right)\right) \Rightarrow \left(\operatorname{Matrix.mulVec}\left(a, x\right) = \left(0: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right)\right)\right)\right) \Rightarrow \left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\exists \left(z: \mathbb{C}\right), \left(\left(\lambda \left(k: \operatorname{Fin}\left(d\right)\right) \mapsto \left(a\left(k, j\right)\right)\right) = \operatorname{SMul.smul}\left(z, v\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.supported_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every column of a Hermitian matrix annihilating the orthogonal complement of a nonzero vector is a complex scalar multiple of that vector.

**Theorem 1.8 (A finite grid supplies a common entangled state).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \mathbb{N}\right), \left(\forall \left(b: \mathbb{N}\right), \left(\left(2 \le a\right) \Rightarrow \left(\left(2 \le b\right) \Rightarrow \left(\left(d = \left(a\right) \cdot \left(b\right)\right) \Rightarrow \left(\exists \left(s: \operatorname{Finset}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in s\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \land \left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right)\right)\right)\right) \land \left(\forall \left(u: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(u \in \operatorname{Matrix.specialUnitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \Rightarrow \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in s\right) \land \left(\forall \left(p: \operatorname{Partition}\left(d\right)\right), \left(\neg \left(\operatorname{Separable}\left(p, \left(\left(u\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Star.star}\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.result` (`✓ std3`). ∎

*Resolves.* `Problems/yu-et-al-2021-absolutely-entangled-all-partitions` (proved) by `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yu-et-al-2021-absolutely-entangled-all-partitions","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Baichu Yu; Pooja Jayachandran; Adam Burchardt; Yu Cai; Nicolas Brunner; Valerio Scarani (2021). *Absolutely entangled sets of pure states for bipartitions and multipartitions*. DOI: [10.1103/PhysRevA.104.032414](https://doi.org/10.1103/PhysRevA.104.032414). URL: <https://arxiv.org/abs/2106.16216v3>.

*Commentary.*

For each partition p, vary the first two local indices over zero and one and fix all remaining local indices at zero. The four resulting global coordinates are distinct: the inverse mixed-radix map recovers the first two indices. For any embedding c of Fin 2 times Fin 2 into Fin d, consider the determinant formed from these four coordinates of a vector: the product at c(0,0) and c(1,1) minus the product at c(0,1) and c(1,0).

Fix a special unitary u. Each coordinate of ux is a linear polynomial in the coordinates of x, so the determinant just described becomes a polynomial of total degree at most two. It is nonzero: let z be the sum of the coordinate vectors at c(0,0) and c(1,1), and evaluate at u* z. The identity uu* = 1 reduces the value to the determinant of z, which is one because the four coordinates are distinct.

A nonzero polynomial of total degree at most m cannot vanish on the whole Cartesian grid with alphabet the complex images of the natural numbers zero through m. Indeed, this alphabet has m + 1 elements. If all grid points were zeros, the Schwartz–Zippel bound would give one at most the total degree divided by m + 1, contradicting the degree bound. Let r be the number of embeddings of Fin 2 times Fin 2 into Fin d and set m = 2r. The product of the determinant polynomials over all these embeddings is nonzero and has total degree at most 2r. Its value at a grid point v is the product of the corresponding determinants of uv. Choose a grid point where this value is nonzero. Then every determinant is nonzero. For d at least four an embedding exists, so v cannot be zero. Hence the same finite grid, with its zero vector removed, works for every u.

For every nonzero grid vector v, divide vv* by its real energy, the sum of the squared complex norms of its coordinates. This energy is positive. The outer product is positive semidefinite and its complex trace is the complex image of the energy, so the normalized matrix is positive semidefinite with trace one. Conjugation by u turns it into the outer product of uv multiplied by the same inverse real energy.

Tensor products of local density matrices are density matrices. For positivity, induct on the set of local factors: the empty product is the outer product of the constant one vector, and adjoining a factor takes the Hadamard product with its reindexed positive semidefinite matrix. For trace one, sum diagonal entries through the mixed-radix equivalence; the sum of products factors into the product of the local traces. Every column of such a tensor product has zero determinant at the four coordinates associated with p: after distributing the products, the first two local factors agree by commutativity and the other factors are identical.

Suppose a nonnegative weighted sum of positive semidefinite matrices equals a real scalar multiple of vv*. If x is orthogonal to v, the quadratic form of this sum at x is zero. Each summand is nonnegative, so a summand with positive weight has zero quadratic form at x and therefore annihilates x. For a Hermitian matrix annihilating every such x and for nonzero v, each column is a complex multiple of v. Explicitly, choose an index i with v(i) nonzero and test the kernel condition on the difference between the k-coordinate vector scaled by the conjugate of v(i) and the i-coordinate vector scaled by the conjugate of v(k). Conjugating the resulting equality and using Hermiticity gives the jth column as v multiplied by its ith entry divided by v(i).

Now suppose a real multiple of vv* is separable for p. If v is zero, its four-coordinate determinant is zero directly. Otherwise write the matrix as a finite convex combination of local density products. Some weight is positive because the weights sum to one. The corresponding product matrix has trace one, so some diagonal entry is nonzero. The kernel argument makes that column z times v for a nonzero complex z. Its four-coordinate determinant is zero by the tensor-product calculation, while scaling a two by two determinant multiplies it by z squared. Since z is nonzero, the determinant of v must be zero.

Finally, d = a times b with a and b at least two gives d at least four. Take s to be the image of the nonzero finite grid under the normalization v to vv* divided by its energy. All its members are density matrices. Given u, choose the grid vector whose transformed determinants are all nonzero. If its conjugated density matrix were separable for any p, the preceding argument would force the determinant at p's four specified coordinates to vanish. Those coordinates give one of the embeddings already excluded. This proves nonseparability for every p simultaneously.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.Partition`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.Separable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.partitionEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.productState`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.summand_kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions.supported_column`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](../AbsolutePPT/QutritPerturbationAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation](../MoreauYosidaFormationSelectiveLoccRefutation.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../../Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate](../../../Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate.md)
