# Finite Phase Mixtures

## Abstract

Small off-diagonal mass admits an exact finite phase mixture.

**Theorem 1.1 (Representation by unit-coordinate outer products).**

$$\forall i,j, H_{ij}=\sum_{a=1}^{n}p_{a}z_{ai}\overline{z_{aj}}, p_{a}\ge0, \sum_{a=1}^{n}p_{a}=1, \Vert z_{ai}\Vert=1, n>0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/FinitePhaseMixture.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be any positive natural number and H any complex Hermitian d by d matrix. Assume every diagonal entry is one and the sum of the norms of H(i,j) over i < j is at most one. There is a positive natural number n, nonnegative real weights indexed by Fin n summing to one, and complex vectors whose every coordinate has norm one, with the displayed exact representation for every i and j. No positive-semidefinite hypothesis is required.

Uniform independent signs have zero mixed moments at distinct coordinates. For an ordered pair i < j, identify its two sign coordinates and multiply coordinate j by conjugate(H(i,j))/norm(H(i,j)). This leaves only the chosen pair and its conjugate as off-diagonal moments. A zero entry uses phase one and receives weight zero. Mix these pair distributions with weights norm(H(i,j)); the identity sign distribution receives the remaining mass.

The construction uses (1+d squared) times 2 to the d labelled terms, allowing repetitions and zero weights. The index is nonempty even when all pair weights vanish. There is no division by the off-diagonal mass or by its remainder, so dimensions one and two and total masses zero and one are included.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/FinitePhaseMixture.result`
