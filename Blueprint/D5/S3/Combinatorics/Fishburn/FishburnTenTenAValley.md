# FishburnTenTenAValley

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Valley permutations and their insertion positions).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley.a_valley_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley.a_valley_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Suppose two is at most bottom, bottom is less than peak, and peak is at most n. Concatenate the decreasing block from peak through bottom plus one, the entry one, the increasing block from peak plus one through n, and the decreasing block from bottom through two. The resulting permutation is Fishburn and avoids 2143, 1423 and 3124. Inserting n plus one at a position from zero through n preserves these conditions exactly at zero or at n minus bottom plus one.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley.a_valley_forms`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenALayered](FishburnTenTenALayered.md)
