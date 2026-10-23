# The unrestricted two-sided permanent lower bound is false

## Abstract

Two cyclic subgroups of the permutation group on seven points give a negative cross-sum on a complex Hermitian positive semidefinite Gram matrix.

**Definition 1.1 (The full subgroup cross-sum).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (K: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{crossSum}\left(G, K, H\right) = \sum_{sigma: G} \sum_{tau: K} \prod_{i: \operatorname{Fin}\left(n\right)} H\left(sigma\left(i\right), tau\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.crossSum` (`✓ std3`).

*Citation.* Malkoun (2023). *Do these cousins of permanents satisfy the following inequality?*. URL: <https://mathoverflow.net/questions/456248/do-these-cousins-of-permanents-satisfy-the-following-inequality>.

*Commentary.*

For arbitrary subgroups G,K of the permutation group on Fin n, crossSum is the unnormalized sum over every element of G and every element of K. Each summand is the product of H(σ(i),τ(i)) over every index i. Native index i corresponds to the source's label i+1. Subgroup elements are actual bijections of this index set.

**Definition 1.2 (The complete main assertion).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (G: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (K: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \exists (c: \mathbb{R}), (0 < c) \land (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.IsHermitian}\left(H\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(H\right)) \Rightarrow (c \cdot \prod_{i: \operatorname{Fin}\left(n\right)} \operatorname{Complex.re}\left(H\left(i, i\right)\right) \le \operatorname{Complex.re}\left(\operatorname{crossSum}\left(G, K, H\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.claim` (`✓ std3`).

*Citation.* Malkoun (2023). *Do these cousins of permanents satisfy the following inequality?*. URL: <https://mathoverflow.net/questions/456248/do-these-cousins-of-permanents-satisfy-the-following-inequality>.

*Commentary.*

Malkoun's MathOverflow question 456248, revision 8, asks whether for every n and every two subgroups G,K of the symmetric group there exists a real constant c(n,G,K)>0 such that Re(f(G,K,H)) ≥ c(n,G,K) times the diagonal product for every complex Hermitian positive semidefinite H. The constant is chosen before H. No Young-subgroup, rank, sign-of-entry or positive-diagonal restriction is imposed on this universal assertion. The real diagonal interpretation is justified by diagonal_product_eq_real below. The author's Young-subgroup and rank-two interest and the separate trivial-subgroup question are distinct restrictions.

**Theorem 1.3 (The source diagonal product is real).**

$$\forall (n: \mathbb{N}), \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.IsHermitian}\left(H\right)) \Rightarrow (\prod_{i: \operatorname{Fin}\left(n\right)} H\left(i, i\right) = \operatorname{Complex.ofReal}\left(\prod_{i: \operatorname{Fin}\left(n\right)} \operatorname{Complex.re}\left(H\left(i, i\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.diagonal_product_eq_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermitian symmetry gives conjugate(H(i,i))=H(i,i), so each diagonal entry has zero imaginary part. The product of the complex diagonal entries is therefore the real embedding of the product of their real parts. This identity supplies the real interpretation of the source inequality and evaluates the witness's real diagonal product from its complex Gram entries.

**Theorem 1.4 (No such uniform positive constant exists).**

$$\neg(\forall (n: \mathbb{N}), \forall (G: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (K: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)), \exists (c: \mathbb{R}), (0 < c) \land (\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.IsHermitian}\left(H\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(H\right)) \Rightarrow (c \cdot \prod_{i: \operatorname{Fin}\left(n\right)} \operatorname{Complex.re}\left(H\left(i, i\right)\right) \le \operatorname{Complex.re}\left(\operatorname{crossSum}\left(G, K, H\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/malkoun-2023-subgroup-permanent-lower-bound` (refuted) by `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"malkoun-2023-subgroup-permanent-lower-bound","declaration_gid":"D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Malkoun (2023). *Do these cousins of permanents satisfy the following inequality?*. URL: <https://mathoverflow.net/questions/456248/do-these-cousins-of-permanents-satisfy-the-following-inequality>.

*Commentary.*

Take n=7. In the source's one-based labels, let G and K be generated by the cycles (1 2 5 6 4 3 7) and (1 2 7 5 6 4 3). Their zero-based arrays are (1,4,6,2,5,3,0) and (1,6,0,2,5,3,4). Both generators have order seven. Let V have columns (1,2),(3,2),(1,−2),(3,2),(1,0),(1,−3),(3,−2), embedded in ℂ. Then H=VᴴV is a complex 7 by 7 Hermitian positive semidefinite matrix by the Gram-positivity theorem. The superscript H denotes conjugate transpose; V has two rows, while H has exactly the square dimensions required by the question. The diagonal entries are (5,13,5,13,1,10,13) and their product is 549250. The canonical equivalence between Fin(orderOf g) and Subgroup.zpowers g reindexes each full subgroup sum by its seven powers. Exact evaluation of the 49 products gives crossSum(G,K,H)=−23944. Hence any proposed c>0 would force 549250c≤−23944, a contradiction. The same fixed H defeats every positive c for this fixed pair G,K. Both subgroups are nontrivial cyclic groups of order seven, so the trivial-group and Young-subgroup restrictions remain outside this result. The additional unrestricted strict-positivity question fails on this same matrix; it is the same counterexample family.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.crossSum`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.diagonal_product_eq_real`
- Truth anchor: `D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result`
