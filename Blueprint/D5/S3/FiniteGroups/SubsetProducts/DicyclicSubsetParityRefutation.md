# An odd total refutes universal dicyclic subset parity

## Abstract

The three subset classes in Mandal--Neetu Question 6.3 cannot all have even counts: Dic12 has 495 four-element subsets.

The five finite-set definitions fix the operations and counts used by the exact affirmative claim and its literal negation.

**Definition 1.1 (The duplicate-free product set).**

$$\forall (G : Type*) [\operatorname{Group}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] , (\forall (A : \operatorname{Finset}\left(G\right)), ((\operatorname{productSet}\left(A\right) : \operatorname{Finset}\left(G\right)) = Finset.image\left(((xy : G \times G) \mapsto xy.1 \cdot xy.2), Finset.product\left(A, A\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.productSet` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

For an implicit G : Type* in any universe, with instances [Group G] and [DecidableEq G], and A : Finset G, productSet A : Finset G is (A.product A).image (fun xy => xy.1 * xy.2). The image ranges over every ordered pair in A times A and removes repeated values; it neither requires distinct factors nor assumes commutativity or finiteness of G. This is the paper's product interpretation of A+A, Main.tex line 120.

**Definition 1.2 (The duplicate-free right quotient set).**

$$\forall (G : Type*) [\operatorname{Group}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] , (\forall (A : \operatorname{Finset}\left(G\right)), ((\operatorname{rightQuotientSet}\left(A\right) : \operatorname{Finset}\left(G\right)) = Finset.image\left(((xy : G \times G) \mapsto xy.1 \cdot (xy.2)^{-1}), Finset.product\left(A, A\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.rightQuotientSet` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

For an implicit G : Type* in any universe, with instances [Group G] and [DecidableEq G], and A : Finset G, rightQuotientSet A : Finset G is (A.product A).image (fun xy => xy.1 * xy.2⁻¹). Every ordered pair is included and repeated values are removed. The inverse is on the second factor, on the right of the first; no commutativity or finiteness of G is assumed. This is A-A as defined in Main.tex line 120.

**Definition 1.3 (All sum-dominant subsets of a given size).**

$$\forall (G : Type*) [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] , (\forall (m : \mathbb{N}), ((\operatorname{sumDominantCount}\left(G, m\right) : \mathbb{N}) = Finset.card\left(Finset.filter\left(((A : \operatorname{Finset}\left(G\right)) \mapsto Finset.card\left(\operatorname{productSet}\left(A\right)\right) > Finset.card\left(\operatorname{rightQuotientSet}\left(A\right)\right)), Finset.powersetCard\left(m, (Finset.univ : \operatorname{Finset}\left(G\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.sumDominantCount` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

For explicit G : Type* in any universe, instances [Group G], [Fintype G] and [DecidableEq G], and m : ℕ, sumDominantCount G m : ℕ is ((univ : Finset G).powersetCard m |>.filter (fun A => (rightQuotientSet A).card < (productSet A).card)).card. The displayed greater-than comparison is the same strict inequality with its sides reversed. The local Classical.propDecidable instance decides the filter. Every distinct m-element subset of G is considered once, without a type restriction or symmetry quotient. The definition applies to every natural m, with no bounds imposed here. It represents S in Main.tex lines 183–187.

**Definition 1.4 (All difference-dominant subsets of a given size).**

$$\forall (G : Type*) [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] , (\forall (m : \mathbb{N}), ((\operatorname{differenceDominantCount}\left(G, m\right) : \mathbb{N}) = Finset.card\left(Finset.filter\left(((A : \operatorname{Finset}\left(G\right)) \mapsto Finset.card\left(\operatorname{productSet}\left(A\right)\right) < Finset.card\left(\operatorname{rightQuotientSet}\left(A\right)\right)), Finset.powersetCard\left(m, (Finset.univ : \operatorname{Finset}\left(G\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.differenceDominantCount` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

For explicit G : Type* in any universe, instances [Group G], [Fintype G] and [DecidableEq G], and m : ℕ, differenceDominantCount G m : ℕ is ((univ : Finset G).powersetCard m |>.filter (fun A => (productSet A).card < (rightQuotientSet A).card)).card. The comparison is strict. The local Classical.propDecidable instance decides the filter. Every distinct m-element subset is considered once, without a type restriction or symmetry quotient, for every natural m without further bounds. This is D in Main.tex lines 183–187.

**Definition 1.5 (All balanced subsets of a given size).**

$$\forall (G : Type*) [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] , (\forall (m : \mathbb{N}), ((\operatorname{balancedCount}\left(G, m\right) : \mathbb{N}) = Finset.card\left(Finset.filter\left(((A : \operatorname{Finset}\left(G\right)) \mapsto Finset.card\left(\operatorname{productSet}\left(A\right)\right) = Finset.card\left(\operatorname{rightQuotientSet}\left(A\right)\right)), Finset.powersetCard\left(m, (Finset.univ : \operatorname{Finset}\left(G\right))\right)\right)\right)))$$

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.balancedCount` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

For explicit G : Type* in any universe, instances [Group G], [Fintype G] and [DecidableEq G], and m : ℕ, balancedCount G m : ℕ is ((univ : Finset G).powersetCard m |>.filter (fun A => (productSet A).card = (rightQuotientSet A).card)).card. The local Classical.propDecidable instance decides this equality filter. Every distinct m-element subset is considered once, without a type restriction or symmetry quotient, for every natural m without further bounds. This is B in Main.tex lines 183–187.

**Definition 1.6 (The full affirmative answer to Question 6.3).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.claim`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.claim` (`✓ std3`).

*Citation.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

Mandal and Neetu, arXiv:2602.09073v1, Question 6.3, ask whether all three counts S, D and B are even for every positive integer n at least three and every integer m between two and 2n inclusive. The claim includes both odd and even n. Its natural-number bounds imply positivity; the local NeZero n instance only supplies the finite-group structure.

QuaternionGroup n is Mathlib's dicyclic group of order 4n, with generators a and x corresponding to the paper's a and b. The paper writes A+A for the product set of all xy with x,y in A, and A-A for the right quotient set of all x times the inverse of y. Finset images remove duplicates. The universe is univ.powersetCard m: every distinct m-element subset of the actual group appears once, without a type restriction or quotient by symmetry.

sumDominantCount counts subsets with product cardinality strictly larger than right quotient cardinality; differenceDominantCount uses strictly smaller, and balancedCount uses equality. The assertion is the conjunction of Even on these three natural counts. It uses the paper's unrestricted S, D and B, rather than its separately defined counts restricted to a given type.

**Theorem 1.7 (The instance n = 3 and m = 4 contradicts the conjunction).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mandal-neetu-dicyclic-question-63-refutation` (refuted) by `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mandal-neetu-dicyclic-question-63-refutation","declaration_gid":"D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sagar Mandal and Neetu (2026). *Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups*. DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073). URL: <https://arxiv.org/abs/2602.09073v1>.

*Commentary.*

The result has type Not claim. For any finite collection and two natural-valued functions, the comparisons greater, smaller and equal partition that collection. The private comparison_partition identity expresses this by two filter-cardinality splits. Applied to product and right quotient cardinalities on all m-subsets, counts_total gives S + D + B = choose(card G,m), using Finset.card_powersetCard.

Take n = 3 and m = 4, which satisfy every stated bound. QuaternionGroup.card gives card G = 12, so the total is choose(12,4) = 495. If all three counts were even, their sum would be even. The odd total contradicts that consequence and refutes the universal affirmative answer.

This argument does not identify an individual odd class, enumerate a group table, or assert that any particular count is always odd. It leaves the paper's preceding m = 2,3 observations and its other questions separate. An even total alone would not imply that all three counts are even. The source note fixes the cited version and interpretation; no first-resolution or worldwide priority claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.balancedCount`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.differenceDominantCount`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.productSet`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.rightQuotientSet`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.sumDominantCount`
