# The Generating Tree of Sortable Permutations

## Abstract

Maximum deletion and insertion give an invertible generating tree with the Schroeder succession rule.

**Definition 1.1 (The parent and insertion site correspondence).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackTree.parentSiteEquiv`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackTree.parentSiteEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every nonnegative n, pairs consisting of a sortable permutation of one through n and a gap at which inserting n plus one remains sortable correspond bijectively to sortable permutations of one through n plus one. The forward map inserts the new maximum; the inverse deletes it and records its position.

**Definition 1.2 (Active insertion sites).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackTree.activeSites`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackTree.activeSites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For a word and an entry M, the active sites are the gaps from zero through the word length at which inserting M produces an SC output avoiding 231.

**Theorem 1.3 (Activity at an earlier site).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackTree.earlier_site_activity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackTree.earlier_site_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a word have distinct entries, let M exceed them all, and let L exceed M. Suppose insertion of M at a later gap is sortable, and an earlier gap is positive. Inserting L at the earlier gap after that insertion remains sortable if and only if inserting L there in the original word is sortable and its original output gap is at most that of the later gap.

**Theorem 1.4 (The Schroeder succession rule).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackTree.succession_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackTree.succession_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a word of distinct entries have an SC output avoiding 231, and let M and L satisfy that M exceeds every word entry and L exceeds M. Write k for the number of active sites for M. The positive active sites admit a bijective ranking from zero through k minus two. Inserting M at the beginning gives k plus one active sites for L; insertion at a positive site of rank r gives r plus three active sites for L. Thus a label k has child labels from 3 through k, followed by two copies of k plus one, whenever k is at least two.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackTree.activeSites`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackTree.earlier_site_activity`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackTree.parentSiteEquiv`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackTree.succession_rule`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackPriority](VincularStackPriority.md)
