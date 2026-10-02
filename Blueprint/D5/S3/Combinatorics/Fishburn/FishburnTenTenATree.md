# FishburnTenTenATree

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Structural alternatives for the Fishburn class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenATree.a_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenATree.a_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Every Fishburn permutation of length n at least two avoiding 2143, 1423 and 3124 is increasing, is obtained from the increasing permutation by reversing the interval from low plus one through high with low plus two at most high and high at most n, has the form of a decreasing block from peak through bottom plus one followed by one, an increasing block from peak plus one through n, and a decreasing block from bottom through two with two at most bottom and bottom less than peak and peak at most n, or permits insertion of the next maximum only at position zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenATree.a_classification`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicParents](FishburnBasicParents.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend](FishburnBasicPrepend.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley](FishburnTenTenAValley.md)
