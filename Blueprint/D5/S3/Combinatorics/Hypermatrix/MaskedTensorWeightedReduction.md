# Actual tensor count and the weighted cell sum

## Abstract

Actual tensor count and the weighted cell sum

**Theorem 1.1 (Actual tensor count and the weighted cell sum).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction.masked_tensor_weighted_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction.masked_tensor_weighted_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every finite field F and k at least one, with the two original antitone masks and their full bounds, the cardinality of ActualCarrier equals q to k squared times (q minus one) to 2k times the actual eligible-permutation weight sum. Constructive pencil factors have scalar fibers of size q minus one. Unique triangular and cell coordinates identify the masked parameter set; the two triangular group orders multiply to q to k squared times (q minus one) to 2k plus one. Literal masked-cell elimination supplies the eligible weights, and cancellation of the strictly positive scalar factor yields the tensor count. All equivalences are constructed for these actual matrices; the statement assumes no orbit classification, bijection or count.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction.masked_tensor_weighted_reduction`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount](LiteralMaskedCellCount.md)
- Dependency: [D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers](PencilParameterFibers.md)
- Dependency: [D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization](SoutheastFactorization.md)
