# FishburnTenTenALayered

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (A reversed interval and its insertion positions).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenALayered.a_layered_forms`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenALayered.a_layered_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Suppose low plus two is at most high and high is at most n. Concatenating the increasing block from one through low, the decreasing block from high through low plus one, and the increasing block from high plus one through n gives a Fishburn permutation avoiding 2143, 1423 and 3124. Among insertion positions zero through n, inserting n plus one preserves these conditions exactly at zero or n, or at low when high equals n.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenALayered.a_layered_forms`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone](FishburnTenTenAMonotone.md)
