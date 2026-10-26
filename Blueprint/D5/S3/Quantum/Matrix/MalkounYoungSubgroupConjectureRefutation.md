# A counterexample to the Young-subgroup cross-sum inequality

## Abstract

Fifteen copies of a three-column Gram matrix violate the proposed lower bound for two class-preserving permutation groups.

**Definition 1.1 (Permutations preserving every equivalence class).**

$$\forall (n: \mathbb{N}), (\forall (r: \operatorname{Setoid}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{SetLike.coe}\left((\operatorname{classPreserving}\left(r\right): \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right))\right) = \{(\sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mid \forall (i: \operatorname{Fin}\left(n\right)), (r.r\left(\operatorname{Equiv.toFun}\left(\sigma, i\right), i\right))\}))$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.classPreserving` (`✓ std3`).

*Citation.* Joseph Malkoun (2025). *Finite graphs and configurations of points*. DOI: [10.1016/j.geomphys.2026.105993](https://doi.org/10.1016/j.geomphys.2026.105993). URL: <https://arxiv.org/abs/2508.13472v3>.

*Commentary.*

For an equivalence relation r on Fin n, classPreserving r is the subgroup of permutations that send each index to an equivalent index. Its displayed carrier determines the subgroup: reflexivity gives the identity, transitivity gives closure under composition, and symmetry gives closure under inversion. This is the group defined in the source's TeX line 405. The index i in Fin n corresponds to the source's label i+1.

**Definition 1.2 (The conjectured lower bound in every dimension).**

$$(\operatorname{claim}: \operatorname{Prop}) = (\forall (n: \mathbb{N}), (\forall (r_{1}: \operatorname{Setoid}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (r_{2}: \operatorname{Setoid}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (h: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{Matrix.IsHermitian}\left(h\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(h\right)) \Rightarrow ((\operatorname{Nat.cast}\left(\operatorname{Nat.card}\left(\operatorname{Subtype}\left(\operatorname{SetLike.coe}\left(\operatorname{SemilatticeInf.inf}\left(\operatorname{classPreserving}\left(r_{1}\right), \operatorname{classPreserving}\left(r_{2}\right)\right)\right)\right)\right)\right): \mathbb{R}) \cdot \prod_{i: \operatorname{Fin}\left(n\right)} (\operatorname{Complex.re}\left(h\left(i, i\right)\right)) \le \operatorname{Complex.re}\left(\operatorname{D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation.crossSum}\left(\operatorname{classPreserving}\left(r_{1}\right), \operatorname{classPreserving}\left(r_{2}\right), h\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joseph Malkoun (2025). *Finite graphs and configurations of points*. DOI: [10.1016/j.geomphys.2026.105993](https://doi.org/10.1016/j.geomphys.2026.105993). URL: <https://arxiv.org/abs/2508.13472v3>.

*Commentary.*

For every natural n, every pair of equivalence relations r₁,r₂ on Fin n, and every complex Hermitian positive semidefinite matrix h, the proposed lower bound is the cardinality of the intersection of their class-preserving groups times the product of the real diagonal entries. Here SemilatticeInf.inf is subgroup intersection, Subtype of its carrier is the type of its elements, and Nat.card is its natural-valued cardinality; the displayed Nat.cast includes this cardinality in the reals. The function crossSum is the sum over both full subgroups of the products of h(σ(i),τ(i)), as in TeX lines 407–408. Conjecture D is the inequality at lines 410–412. Hermitian diagonal entries are real: diagonal_product_eq_real identifies their complex product with Complex.ofReal of the product of their real parts. Thus this real inequality expresses the source's diagonal-product inequality without any additional restriction on n or on the relations.

**Theorem 1.3 (Fifteen Gram blocks contradict the bound).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/malkoun-2025-young-subgroup-conjecture-d` (refuted) by `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"malkoun-2025-young-subgroup-conjecture-d","declaration_gid":"D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joseph Malkoun (2025). *Finite graphs and configurations of points*. DOI: [10.1016/j.geomphys.2026.105993](https://doi.org/10.1016/j.geomphys.2026.105993). URL: <https://arxiv.org/abs/2508.13472v3>.

*Commentary.*

Use coordinates (j,s) in Fin m × Fin 3, identified with Fin (m·3) by (j,s) ↦ 3j+s. On each three-point block, the first relation has classes {0,1} and {2}, and the second has classes {0} and {1,2}; indices in different blocks are never equivalent. Let V have columns (1,0), (1,1), (1,Complex.I). Its Gram matrix A = VᴴV has rows (1,1,1), (1,2,1+Complex.I), and (1,1−Complex.I,2). Let H be the direct sum of m copies of A, reindexed by the stated coordinates. Each Gram block is positive semidefinite; block-diagonal assembly and reindexing preserve this property. In particular H is Hermitian.

A family of class-preserving permutations of Fin 3, one for each j, acts on (j,s) by fixing j and applying its jth permutation to s. Conversely, a permutation preserving either block relation fixes the first coordinate, and its restriction to each fiber is a bijection of Fin 3 preserving the corresponding seed relation. These two constructions identify the full class-preserving subgroup with the product of the seed subgroups. Reindexing the product of matrix entries by (j,s) separates it into a product over blocks. Reindexing both subgroup sums by these families, then distributing each finite sum over the product, gives crossSum(H) = crossSum(A)^m for the two corresponding pairs of groups.

For the first seed relation the only permutations are the identity and the swap of 0 and 1; for the second they are the identity and the swap of 1 and 2. Enumerating each group by the two Boolean values reduces the seed cross-sum to four products. They are respectively 4, 2, 2, and 1−Complex.I, so their sum is 9−Complex.I.

If two seed indices are equivalent for both relations, they are equal. A permutation belonging to both block subgroups therefore fixes both coordinates of every index. Their intersection is the identity subgroup and has cardinality one. For the diagonal product, Hermitian symmetry first identifies the real product with its complex embedding. Reindexing the complex product by (j,s) gives the mth power of the seed diagonal product, and the seed diagonal is (1,2,2). Injectivity of Complex.ofReal therefore gives the real diagonal product 4^m.

Exact complex multiplication gives (9−Complex.I)^15 = −20078071648128−224842906547072·Complex.I. Now suppose claim holds and apply it with n = 45, m = 15, the two block relations, and H. The established positivity supplies both matrix hypotheses. Substituting the intersection, diagonal product, block factorization, seed value, and fifteenth power into the asserted inequality gives 1073741824 ≤ −20078071648128, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.classPreserving`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation](MalkounSubgroupLowerBoundRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
