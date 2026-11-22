# Marginal rank on a positive matrix's joint unitary orbit

## Abstract

The minimum marginal rank is the ceiling of the joint rank divided by the traced dimension.

**Theorem 1.1 (Exact least rank after discarding one factor).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank.minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank.minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Acknowledgement.* Ky Fan (1949). *On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I*. DOI: [10.1073/pnas.35.11.652](https://doi.org/10.1073/pnas.35.11.652). URL: <https://pmc.ncbi.nlm.nih.gov/articles/PMC1063101/>.

*Commentary.*

For every positive semidefinite matrix on the product of spaces of dimensions m and e, with e positive, the least rank attainable by conjugating by a joint unitary and tracing out the second space is the ceiling of rank(X)/e. The statement includes zero matrices.

Diagonalize the retained marginal by a local unitary. Any zero diagonal entry is a sum of nonnegative joint diagonal entries, so all the joint entries above that coordinate vanish. Positivity then forces the corresponding joint rows to vanish. This bounds the joint rank by e times the marginal rank.

For attainment, use a joint eigenbasis and a permutation to put all nonzero eigenvalues in successive rows of the product basis. The number of occupied rows is the ceiling. Reeb and Wolf group eigenvalues into product rows in Section 3.3 after Proposition 5. Fan's variational principle gives the spectral bound underlying the rank obstruction.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank.minimum`
- Dependency: [D5/S3/Quantum/Information/PartialTrace/Isometries](../../Information/PartialTrace/Isometries.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels](../../ProcessReconstruction/ReconstructionChannels.md)
