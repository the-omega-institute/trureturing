# BlockCounting

## Abstract

A complete conjugacy partition and its central twisted-inversion blocks factor the count of all good maps.

**Definition 1.1 (A complete block certificate).**

Lean statement: `D5/S3/FiniteGroups/Quandles/BlockCounting.Data`

*Formalization.* `D5/S3/FiniteGroups/Quandles/BlockCounting.Data` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Data records representatives, a conjugacy-invariant classifier, a conjugator from the classified representative to every element, an equivalence with the actual center, and every central twisted-inversion destination. It assumes no counts.

**Definition 1.2 (All compatible labels on one block).**

Lean statement: `D5/S3/FiniteGroups/Quandles/BlockCounting.Local`

*Formalization.* `D5/S3/FiniteGroups/Quandles/BlockCounting.Local` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

For a block C_b and center alphabet Z, Local consists of every function f:C_b→Z satisfying f(dest(b,i,f(i)))=f(i) for every i. When two classes are paired, their common central label is chosen once.

**Definition 1.3 (Global labels are independent local assignments).**

Lean statement: `D5/S3/FiniteGroups/Quandles/BlockCounting.labelBlockEquiv`

*Formalization.* `D5/S3/FiniteGroups/Quandles/BlockCounting.labelBlockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

The representatives restrict a global central label to each block. The classifier extends local assignments to all group elements. The conjugator and center equivalence prove that restriction and extension are mutual inverses. This includes all labels, not a selected subfamily.

**Theorem 1.4 (The complete product formula).**

$$\operatorname{NatCard}\left(\operatorname{Good}\left(G\right)\right) = \prod_{b\in B} \operatorname{NatCard}\left(\operatorname{Local}\left(\operatorname{dest}\left(D\right), b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/BlockCounting.good_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

For any group G, complete certificate D:Data G B Z C, and finite set B of blocks, the cardinality of all good maps is the product of the cardinalities of the local compatible-label types. Empty and zero-count blocks are included. Each local factor is the central-label form of the weighted involution sum; a paired edge carries one common label.

**Theorem 1.5 (The product formula on the existing interface).**

$$\operatorname{NatCard}\left(\operatorname{WholeGood}\left(G\right)\right) = \prod_{b\in B} \operatorname{NatCard}\left(\operatorname{Local}\left(\operatorname{dest}\left(D\right), b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/BlockCounting.whole_good_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

For finite G with decidable equality, WholeGood(G) in the display abbreviates the existing Good subtype on Finset.univ. The same exact product formula applies to it. It is used by both numerical counts in the complete Problem 11.6 refutation.

**Definition 1.6 (The native conjugacy-class quotient).**

Lean statement: `D5/S3/FiniteGroups/Quandles/BlockCounting.classEquiv`

*Formalization.* `D5/S3/FiniteGroups/Quandles/BlockCounting.classEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

The certificate gives an equivalence from Mathlib ConjClasses G to the disjoint union of block indices. Thus the class count used in the refutation is the actual class number.

## References

- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.Data`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.Local`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.classEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.good_card`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.labelBlockEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/BlockCounting.whole_good_card`
- Dependency: [D5/S3/FiniteGroups/Quandles/CentralLabels](CentralLabels.md)
