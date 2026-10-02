# The Binomial-Catalan Enumeration

## Abstract

The binomial transform of the Catalan numbers enumerates two classes of pattern-avoiding Fishburn permutations.

**Definition 1.1 (The binomial-Catalan sum).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.binomialCatalan`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.binomialCatalan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every nonnegative integer n, the binomial-Catalan sum is the sum over k from one through n of the binomial coefficient choosing k minus one from n minus one multiplied by the Catalan number of index n minus k. The sum is zero when n is zero.

**Definition 1.2 (The two avoidance classes).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.claim1013`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.claim1013` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every positive integer n, the number of Fishburn permutations of length n avoiding 2413 and 2431 and the number avoiding 2431 and 3241 both equal the binomial-Catalan sum at n.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.binomialCatalan`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.claim1013`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnDefs](FishburnDefs.md)
