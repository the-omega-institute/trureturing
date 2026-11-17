# First letters at a fixed major index

## Abstract

Major-index first-letter expectations have the monic rational form of Conjecture 5.2.

Permutations are Equiv.Perm (Fin n). Position i has one-based letter (pi i).val+1. The adjacent-descent indicator is D5.S1.Words.Patterns.Separable.CutFactorization.descentAt. All casts displayed with codomain Q are natural-number casts into the rational field.

**Definition 1.1 (The major index).**

$$\forall n \in \mathbb{N},\; \forall pi \in \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{maj}\left(pi\right) = \sum_{i: \operatorname{Fin}\left(n\right)} (\operatorname{val}\left(i\right) + 1) \cdot \operatorname{D5.S1.Words.Patterns.Separable.CutFactorization.descentAt}\left(pi, i\right)$$

*Formalization.* `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.maj` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Section 5.2, page 19: “Below, we have given conjectures about two: the major index and the inversion number.” The major index is the sum of one-based positions at which an adjacent descent occurs. The final position has descent indicator zero.

**Definition 1.2 (The conditioning cardinality).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{count}\left(n, k\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right) \mapsto \operatorname{maj}\left(pi\right) = k), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.count` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” Here the statistic is maj. Each permutation occurs once in the finite set, which retains exactly major index k.

**Definition 1.3 (The conditional expectation).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{E}\left(n, k\right) = \frac{\sum_{pi \in \operatorname{Finset.filter}\left((pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right) \mapsto \operatorname{maj}\left(pi\right) = k), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)} (\operatorname{Nat.cast}\left(\operatorname{if} h: 0 < n \operatorname{then} \operatorname{val}\left(pi\left(\operatorname{Fin.mk}\left(0, h\right)\right)\right) + 1 \operatorname{else} 0\right): \mathbb{Q})}{(\operatorname{Nat.cast}\left(\operatorname{count}\left(n, k\right)\right): \mathbb{Q})}$$

*Formalization.* `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.E` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” Here the statistic is maj. Division takes place in Q; the theorem restricts to nonempty conditioning sets.

**Definition 1.4 (Conjecture 5.2).**

$$claim = (\forall k \in \mathbb{N},\; 0 < k \implies \exists P \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \exists Q \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \operatorname{Polynomial.Monic}\left(P\right) \land \operatorname{Polynomial.Monic}\left(Q\right) \land \operatorname{Polynomial.natDegree}\left(P\right) = k + 1 \land \operatorname{Polynomial.natDegree}\left(Q\right) = k \land \forall n \in \mathbb{N},\; k \le n \implies \operatorname{count}\left(n, k\right) \neq 0 \implies \operatorname{E}\left(n, k\right) = \frac{\operatorname{Polynomial.eval}\left((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}), P\right)}{((\operatorname{Nat.cast}\left(k\right): \mathbb{Q}) + 1: \mathbb{Q}) \cdot \operatorname{Polynomial.eval}\left((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}), Q\right)})$$

*Formalization.* `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.claim` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Conjecture 5.2, page 20: “For fixed k > 0 and n ≥ k, E[π(1) | π ∈ S_n, maj(π) = k] satisfies a rational function in n that is 1/(k + 1) times the quotient of a monic degree-(k + 1) polynomial by a monic degree-k polynomial.” The nonzero cardinality hypothesis expresses that the conditional expectation is defined. The quotient need not be reduced, and n=k is included whenever the conditioning set is nonempty.

**Theorem 1.5 (The monic rational form).**

$$\forall k \in \mathbb{N},\; 0 < k \implies \exists P \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \exists Q \in \operatorname{Polynomial}\left(\mathbb{Q}\right),\; \operatorname{Polynomial.Monic}\left(P\right) \land \operatorname{Polynomial.Monic}\left(Q\right) \land \operatorname{Polynomial.natDegree}\left(P\right) = k + 1 \land \operatorname{Polynomial.natDegree}\left(Q\right) = k \land \forall n \in \mathbb{N},\; k \le n \implies \operatorname{count}\left(n, k\right) \neq 0 \implies \operatorname{E}\left(n, k\right) = \frac{\operatorname{Polynomial.eval}\left((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}), P\right)}{((\operatorname{Nat.cast}\left(k\right): \mathbb{Q}) + 1: \mathbb{Q}) \cdot \operatorname{Polynomial.eval}\left((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}), Q\right)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result` (`✓ std3`). ∎

*Resolves.* `Problems/kagey-2021-first-letter-expectation-conjectures-5-1-5-2` (proved) by `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey-2021-first-letter-expectation-conjectures-5-1-5-2","declaration_gid":"D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Increasing blocks give the cardinality and first-letter weighted sum as polynomials in n. Exact-descent inclusion–exclusion selects major index k. Only S=U={k} contributes to the highest coefficients, which are 1/k! and 1/(k+1)!. Scaling by these factorials gives monic Q and P of the required degrees. The source's n=k endpoint is retained.

## References

- Truth anchor: `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.E`
- Truth anchor: `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.claim`
- Truth anchor: `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.count`
- Truth anchor: `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.maj`
- Truth anchor: `D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.result`
- Dependency: [D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629](../../../S0/Asymptotics/GeneratingFunctions/KotesovecA022629.md)
- Dependency: [D5/S1/Words/Patterns/Separable/CutFactorization](../Patterns/Separable/CutFactorization.md)
- Dependency: [D5/S1/Words/Permutations/OrderedBlockAllocations](OrderedBlockAllocations.md)
