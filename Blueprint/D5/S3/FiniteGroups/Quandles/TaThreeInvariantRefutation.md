# The three invariants do not determine the good-involution count

## Abstract

Two finite nonabelian groups have equal order, center order and class number, but different complete counts of good involutions.

**Definition 1.1 (Two native semidirect products).**

Lean statement: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.Gr`

*Formalization.* `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.Gr` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Gr(false) and Gr(true) are Mathlib semidirect products (Z/16) ⋊ (Z/4). The action generator multiplies the additive first coordinate by 5 or 7, respectively. Multiplication is (i,j)(k,l)=(i+r^j k,j+l). The native group structure proves the group laws; no multiplication-table axioms are introduced.

**Definition 1.2 (Counts of all whole-group good maps).**

Lean statement: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.goodCount`

*Formalization.* `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.goodCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

goodCount(G) is the cardinality of the existing repository Good subtype on Finset.univ. Its maps are involutions commuting with each s_x, and s_(rho(x)) is both a left and right inverse of s_x. Here s_x(y)=xyx^-1. Counts are of functions, without quotienting by quandle isomorphism.

**Theorem 1.3 (Both complete counts).**

$$\operatorname{goodCount}\left(\operatorname{Gr}\left(false\right)\right) = 8847360 \land \operatorname{goodCount}\left(\operatorname{Gr}\left(true\right)\right) = 2160000$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.good_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

The complete central-label bijection and independent-block product prove goodCount(Gr(false))=8847360 and goodCount(Gr(true))=2160000. For r=5 the blocks are one all-one 4-by-4 block, six forced paired 2-by-2 blocks of off-diagonal weight four, and three all-two 2-by-2 blocks. Their factors are 10, 4 and 6, yielding 10*4^6*6^3. For r=7 the blocks are four all-one 4-by-4 blocks and three all-two 2-by-2 blocks, yielding 10^4*6^3. Every conjugacy class and central destination is checked against the actual native groups. Each local factor enumerates at most 4^4 labels; the bijection supplies completeness for all good maps.

**Definition 1.4 (Ta's exact three-invariant determination question).**

Lean statement: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.claim`

*Formalization.* `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Ta, Problem 11.6: Let G be a finite nonabelian group of order n. Is the number of good involutions of Conj G completely determined by n, the order of the center Z(G), and the class number k(G) of G? If so, is there an exact formula to compute this number? The formal claim quantifies over two finite groups, explicitly requires each to be nonabelian, and asserts equality of their whole-group good-map counts whenever their three invariant cardinalities agree. This is the determination part of the original question. Refuting it also rules out a formula depending only on those three numbers.

**Theorem 1.5 (The determination fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ta-2025-problem-11-6-three-invariant-refutation` (refuted) by `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ta-2025-problem-11-6-three-invariant-refutation","declaration_gid":"D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Both native groups are nonabelian and have invariant triple (64,4,22). The center enumerations cover every central element. The complete partitions are equivalent to Mathlib ConjClasses, so 22 is the actual class number. Their complete good-map counts differ. The proof therefore negates the original universal determination assertion. Ta Theorem 6.7 supplies the attributed central-function characterization; our label z is the inverse of Ta's zeta. The result concerns whole conjugation quandles, not a knot classification. The inspected versioned primary literature did not identify a prior answer to 11.6; this bounded check establishes neither worldwide priority nor uniqueness.

## References

- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.Gr`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.goodCount`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.good_counts`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result`
- Dependency: [D5/S3/FiniteGroups/Quandles/BlockCounting](BlockCounting.md)
