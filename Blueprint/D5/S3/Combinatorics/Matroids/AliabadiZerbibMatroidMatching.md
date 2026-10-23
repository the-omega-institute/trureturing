# Aliabadi–Zerbib matroid matching

## Abstract

A sparse paving integer matroid need not be matched to itself.

**Definition 1.1 (IsPaving).**

$$\forall (G: Type), \forall (M: Matroid\left(G\right)), (IsPaving\left(M\right)) \Leftrightarrow (\forall (X: Set\left(G\right)), (X \subseteq \operatorname{M}.\operatorname{E}) \Rightarrow ((\operatorname{X}.\operatorname{encard} + 1 = \operatorname{M}.\operatorname{eRank}) \Rightarrow (\operatorname{M}.\operatorname{Indep}\left(X\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsPaving` (`✓ std3`).

*Citation.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Page 2: “A matroid M = (E, I) of rank n is said to be a paving matroid if every (n − 1)-subset of E is independent.” Here X is a ground subset, X.encard is its extended natural cardinality and M.eRank is the extended natural rank; the size condition is X.encard + 1 = M.eRank.

**Definition 1.2 (IsSparsePaving).**

$$\forall (G: Type), \forall (M: Matroid\left(G\right)), (IsSparsePaving\left(M\right)) \Leftrightarrow ((IsPaving\left(M\right)) \land (IsPaving\left(M^{*}\right)))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsSparsePaving` (`✓ std3`).

*Citation.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Page 2: “If M and M* are both paving matroids then M is called a sparse paving matroid.” The star is Mathlib's matroid dual.

**Definition 1.3 (BasesMatched).**

$$\forall (G: Type), [AddCommGroup\left(G\right)] \forall (M: Matroid\left(G\right)), \forall (n: \mathbb{N}), \forall (a: Fin\left(n\right) \to G), \forall (b: Fin\left(n\right) \to G), (BasesMatched\left(M, a, b\right)) \Leftrightarrow (\forall (i: Fin\left(n\right)), \neg (a\left(i\right) + b\left(i\right) \in \operatorname{M}.\operatorname{E}))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.BasesMatched` (`✓ std3`).

*Citation.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Page 2, Definition 1.3(1): “Let M and N be two matroids over G with r(M) = r(N) = n > 0. Let M = {a₁, . . . , aₙ} and N = {b₁, . . . , bₙ} be ordered bases of M and N, respectively. We say M is matched to N if aᵢ + bᵢ ∉ E(M), for all 1 ≤ i ≤ n.” Indices are Fin n. This predicate is the sum-exclusion clause; IsMatchedTo also requires injectivity and the two basis conditions.

**Definition 1.4 (IsMatchedTo).**

$$\forall (G: Type), [AddCommGroup\left(G\right)] \forall (M: Matroid\left(G\right)), \forall (N: Matroid\left(G\right)), (IsMatchedTo\left(M, N\right)) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (a: Fin\left(n\right) \to G), (\operatorname{Function}.\operatorname{Injective}\left(a\right)) \Rightarrow ((\operatorname{M}.\operatorname{IsBase}\left(\operatorname{Set}.\operatorname{range}\left(a\right)\right)) \Rightarrow (\exists (b: Fin\left(n\right) \to G), (\operatorname{Function}.\operatorname{Injective}\left(b\right)) \land ((\operatorname{N}.\operatorname{IsBase}\left(\operatorname{Set}.\operatorname{range}\left(b\right)\right)) \land (BasesMatched\left(M, a, b\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsMatchedTo` (`✓ std3`).

*Citation.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Page 2, Definition 1.3(2): “We say that M is matched to N if for every basis M of M there exists a basis N of N, so that M is matched to N.” An ordered basis is an injective Fin n enumeration whose Set.range is a Mathlib base. The existential ordering of the target includes all possible permutations.

**Definition 1.5 (claim).**

$$(claim) \Leftrightarrow (\forall (G: Type), [AddCommGroup\left(G\right)] [IsAddTorsionFree\left(G\right)] \forall (M: Matroid\left(G\right)), \forall (N: Matroid\left(G\right)), (\operatorname{M}.\operatorname{Finite}) \Rightarrow ((\operatorname{N}.\operatorname{Finite}) \Rightarrow ((\operatorname{M}.\operatorname{Loopless}) \Rightarrow ((\operatorname{N}.\operatorname{Loopless}) \Rightarrow ((0 < \operatorname{M}.\operatorname{eRank}) \Rightarrow ((\operatorname{M}.\operatorname{eRank} = \operatorname{N}.\operatorname{eRank}) \Rightarrow ((IsSparsePaving\left(N\right)) \Rightarrow (((\operatorname{Set}.\operatorname{ncard}\left(\operatorname{M}.\operatorname{E}\right) + 1 = \operatorname{Set}.\operatorname{ncard}\left(\operatorname{N}.\operatorname{E}\right)) \lor (\operatorname{Set}.\operatorname{ncard}\left(\operatorname{M}.\operatorname{E}\right) = \operatorname{Set}.\operatorname{ncard}\left(\operatorname{N}.\operatorname{E}\right))) \Rightarrow ((\neg ((0: G) \in \operatorname{N}.\operatorname{E})) \Rightarrow (IsMatchedTo\left(M, N\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.claim` (`✓ std3`).

*Citation.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Page 5, Question 2.7: “Let G be an abelian torsion-free group. Let M be a matroid over G and N be a sparse paving matroid over G, both of the same rank n, so that |E(M)| = |E(N)| − 1 or |E(M)| = |E(N)|. If 0 ∉ E(N), is M matched to N?” The proposition is the positive answer in the paper's standing finite, loopless setting, with positive common rank. The first size alternative uses addition of one to the smaller cardinality. IsAddTorsionFree is Mathlib's additive torsion-free class.

**Theorem 1.6 (result).**

$$\neg (\forall (G: Type), [AddCommGroup\left(G\right)] [IsAddTorsionFree\left(G\right)] \forall (M: Matroid\left(G\right)), \forall (N: Matroid\left(G\right)), (\operatorname{M}.\operatorname{Finite}) \Rightarrow ((\operatorname{N}.\operatorname{Finite}) \Rightarrow ((\operatorname{M}.\operatorname{Loopless}) \Rightarrow ((\operatorname{N}.\operatorname{Loopless}) \Rightarrow ((0 < \operatorname{M}.\operatorname{eRank}) \Rightarrow ((\operatorname{M}.\operatorname{eRank} = \operatorname{N}.\operatorname{eRank}) \Rightarrow ((IsSparsePaving\left(N\right)) \Rightarrow (((\operatorname{Set}.\operatorname{ncard}\left(\operatorname{M}.\operatorname{E}\right) + 1 = \operatorname{Set}.\operatorname{ncard}\left(\operatorname{N}.\operatorname{E}\right)) \lor (\operatorname{Set}.\operatorname{ncard}\left(\operatorname{M}.\operatorname{E}\right) = \operatorname{Set}.\operatorname{ncard}\left(\operatorname{N}.\operatorname{E}\right))) \Rightarrow ((\neg ((0: G) \in \operatorname{N}.\operatorname{E})) \Rightarrow (IsMatchedTo\left(M, N\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohsen Aliabadi; Shira Zerbib (2024). *Matchings in matroids over abelian groups*. DOI: [10.1007/s10801-024-01308-z](https://doi.org/10.1007/s10801-024-01308-z). URL: <https://arxiv.org/abs/2202.07719v3>.

*Commentary.*

Over ℤ, let E = {1, …, n + s} and H = {s + 1, …, s + n}, with n, s ≥ 2. The bases are exactly the n-element subsets of E other than H. A two-exchange argument constructs a matroid; extension of smaller sets and complementary bases show that it and its dual are paving. For a in {1, …, n}, b in E and a + b outside E, one has b in H. Thus an injective n-tuple of targets has range H, which is not a base. Taking M = N at n = s = 2 disproves the proposition.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.BasesMatched`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsMatchedTo`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsPaving`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.IsSparsePaving`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.result`
