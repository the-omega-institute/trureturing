# Signed parity separates Walsh hit laws and generators

## Abstract

Even-parity hit masses impose a quantitative signed inequality and an exact test for negative type.

**Theorem 1.1 (A negative generator rate follows from a finite crossing cancellation).**

$$gamma < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh.generator_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Invert the negative cut-rank function on the finite vertex-mask group. When the class and singleton cuts have rank one and every straddling pair cut has rank two, odd total labels have zero weight. The signed mass of odd class parity is one half, but every crossing pair has zero signed mass.

On every even label, that parity indicator is bounded by the number of pairs crossing the class. The two mass values therefore force at least one negative rate on an even label meeting both sides. This conclusion uses exact finite character inversion, not a derivative or small-time approximation.

This helper module also proves that a translation kernel is conditionally negative definite exactly when its nontrivial inverse negative Fourier coefficients are nonnegative. The proof diagonalizes the full finite quadratic form into character squares.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh.generator_gap`
