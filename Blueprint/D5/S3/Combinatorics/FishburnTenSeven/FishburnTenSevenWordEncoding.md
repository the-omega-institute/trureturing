# FishburnTenSevenWordEncoding

## Abstract

Three-letter words allocate entries to decreasing, increasing and trailing decreasing blocks.

**Definition 1.1 (Blocks determined by a word).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.blocks`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.blocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For a word indexed from zero through size minus one, assign the value index plus two to the block indicated by its letter. The d and j blocks list their assigned values in decreasing order, and the i block lists its assigned values in increasing order.

**Definition 1.2 (Encoding three blocks).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodeBlocks`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodeBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For three lists and an index from zero through size minus one, the encoded letter is d if index plus two belongs to the first list, i if it belongs to the second list but not the first, and j otherwise.

**Definition 1.3 (Reconstructing a permutation).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.reconstruct`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For a word of length size and a total, reconstruction concatenates the decreasing interval with entries from size plus three through total, the d block, one, the i block, size plus two, and the j block. The initial interval is empty when total is at most size plus two.

**Definition 1.4 (Encoding a permutation around one and the peak).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodePermutation`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodePermutation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Cut the list at its first one, taking the whole list as the initial block when one is absent. The middle block is the portion after that one and before the first subsequent entry size plus two, or the whole remaining portion when that entry is absent. For an index from zero through size minus one, encode index plus two as d when it belongs to the initial block, as i when it instead belongs to the middle block, and as j otherwise.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.blocks`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodeBlocks`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.encodePermutation`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.reconstruct`
- Dependency: [D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords](FishburnTenSevenWords.md)
