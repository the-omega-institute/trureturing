# Integer Inner Inverses from Unit Minors

## Abstract

A maximal nonzero minor of a finite totally unimodular integer matrix reconstructs the whole matrix and gives an integer inner inverse.

**Theorem 1.1 (Every finite TU integer matrix has an integer inner inverse).**

$$\forall m, n: Type, [\operatorname{Fintype}\left(m\right)], [\operatorname{Fintype}\left(n\right)], \forall A: \operatorname{Matrix}\left(m, n, \mathbb{Z}\right), \operatorname{IsTotallyUnimodular}\left(A\right) \Rightarrow \exists B: \operatorname{Matrix}\left(n, m, \mathbb{Z}\right), A B A = A$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse.exists_integer_inner_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

Choose a maximal nonzero square minor. The empty minor has determinant one, and injective row selection bounds its size, so this choice also covers the zero matrix. Total unimodularity makes the chosen determinant plus or minus one, and the minor therefore has an inverse over the integers.

Bordering the minor by any remaining row and column gives a larger minor whose determinant vanishes by maximality. The Schur determinant identity then forces every residual entry to vanish. Place the selected inverse in a transposed zero block matrix and transport it back to the original coordinates.

The row and column types may be empty, and the matrix may be rectangular or rank deficient. No nonzero-entry or full-rank hypothesis is needed. The conclusion is only ABA equals A: it asserts neither Moore–Penrose conditions nor norm optimality.

Fampa and Lee supply the real selected-minor construction; Sontag supplies the splitting and maximal-minor-ideal context. The integral TU result combines unit determinants with bordered-minor reconstruction and carries no originality claim.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse.exists_integer_inner_inverse`
