# Two rectangular blocks with independent history length

## Abstract

The nonzero spectrum of the two-block constant-delay history matrix is obtained by taking roots of the rectangular product spectrum.

Let U have m rows and n columns, and let V have n rows and m columns. The equivalence blockEquiv sends a left sum coordinate to block zero and a right sum coordinate to block one. The real matrix zeroDiagonal U V is the reindexing of Matrix.fromBlocks 0 U V 0 along this equivalence. Thus it uses exactly the dependent block coordinates of asyncMatrix. The delay array has rows (0,b) and (a,0): a is the delay from block one to block zero. The history contains every slot from zero through K, independently of a and b.

**Theorem 1.1 (The literal history matrix and the rectangular product).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (K: \mathbb{N}), (\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (\forall (V: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), ((a \le K) \to ((b \le K) \to (\forall (z: \mathbb{C}), ((z \ne (0: \mathbb{C})) \to (z \in \operatorname{spectrum}\left(\mathbb{C}, \operatorname{Matrix.map}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum.zeroDiagonal}\left(U, V\right), \begin{pmatrix}0&b\\a&0\end{pmatrix}, K\right), \operatorname{DFunLike.coe}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right)\right) \Leftrightarrow z^{a + b + 2} \in \operatorname{spectrum}\left(\mathbb{C}, \operatorname{Matrix.map}\left(U \cdot V, \operatorname{DFunLike.coe}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum.nonzero_spectrum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift rows reconstruct the entire history from its newest slot using inverse powers of a nonzero spectral value. The two update rows then yield a product eigenvector in the first block. Conversely, a product eigenvector lifts to the history by setting its second block to the product of the appropriate inverse power and V applied to the first block. The argument applies to arbitrary rectangular matrices, including empty or singular blocks. It asserts no correspondence at zero and no equality of algebraic multiplicities.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum.nonzero_spectrum_iff`
- Dependency: [D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation](AsynchronousIterationSpectralRadiusRefutation.md)
