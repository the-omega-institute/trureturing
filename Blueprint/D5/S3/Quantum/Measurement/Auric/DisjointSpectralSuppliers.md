# Flat factors and spectral Jensen bounds

## Abstract

Flat factors and spectral Jensen bounds

**Theorem 1.1 (Flat factors with arbitrary row capacity).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.exists_flat_rows_of_rank_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.exists_flat_rows_of_rank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2003). *Principal Submatrices of a Hermitian Matrix*. DOI: [10.1080/0308108031000069164](https://doi.org/10.1080/0308108031000069164). URL: <https://doi.org/10.1080/0308108031000069164>.

*Acknowledgement.* Pedro G. Massey (2010). *Non-commutative Schur–Horn theorems and extended majorization for Hermitian matrices*. DOI: [10.1080/03081080802677615](https://doi.org/10.1080/03081080802677615). URL: <https://arxiv.org/abs/0712.2246>.

*Commentary.*

A positive semidefinite matrix A with rank at most m has a factor V with m rows, V†V = A and constant diagonal Tr(A)/m in VV†. The positive-capacity construction uses Fourier columns. When m = 0, A is zero and the row type is empty.

**Theorem 1.2 (Concave sums of Gram eigenvalues).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.gram_spectral_sum_le_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.gram_spectral_sum_le_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If V†V is a contraction, a concave function on [0,1] vanishing at zero can be summed on the column Gram and bounded by its sum on the row Gram diagonal. The rectangular spectrum comparison establishes the upper spectral endpoint for the row Gram, and diagonal Jensen uses the squared moduli of its diagonalizing unitary.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.exists_flat_rows_of_rank_le`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.gram_spectral_sum_le_diagonal`
- Dependency: [D5/S3/Quantum/Measurement/Auric/EqualBlockProjection](EqualBlockProjection.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProjectiveRecord](ProjectiveRecord.md)
