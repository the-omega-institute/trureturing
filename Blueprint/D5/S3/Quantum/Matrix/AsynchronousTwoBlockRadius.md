# The two-block delay radius and the original power bound

## Abstract

The exact spectral radius of a two-block zero-diagonal history operator depends on the sum of its two remote delays.

**Theorem 1.1 (Exact radius for every sufficiently long history).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (K: \mathbb{N}), ((0 < m) \to ((0 < n) \to (\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (\forall (V: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)), ((1 \le a) \to ((1 \le b) \to ((a \le k) \to ((b \le k) \to ((a \le K) \to ((b \le K) \to (\forall (lambda: \mathbb{R}), ((0 < lambda) \to ((lambda < 1) \to ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum.zeroDiagonal}\left(U, V\right)\right) = \operatorname{ENNReal.ofReal}\left(lambda\right)) \to ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum.zeroDiagonal}\left(U, V\right), \begin{pmatrix}0&b\\a&0\end{pmatrix}, K\right)\right) = \operatorname{ENNReal.ofReal}\left(lambda^{\frac{(2: \mathbb{R})}{(\operatorname{Nat.cast}\left(a + b + 2\right): \mathbb{R})}}\right)) \land ((\operatorname{ENNReal.ofReal}\left(lambda^{\frac{(2: \mathbb{R})}{(\operatorname{Nat.cast}\left(a + b + 2\right): \mathbb{R})}}\right) \le \operatorname{ENNReal.ofReal}\left(lambda^{\frac{(1: \mathbb{R})}{(\operatorname{Nat.cast}\left(k\right): \mathbb{R}) + (1: \mathbb{R})}}\right)) \land (\operatorname{ENNReal.ofReal}\left(lambda^{\frac{(1: \mathbb{R})}{(\operatorname{Nat.cast}\left(k\right): \mathbb{R}) + (1: \mathbb{R})}}\right) < 1))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AsynchronousTwoBlockRadius.two_block_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block sizes m and n are positive. The real rectangular matrices U and V are arbitrary. The matrix zeroDiagonal U V is the explicit reindexing of Matrix.fromBlocks 0 U V 0 into the dependent block coordinates. The delay array has rows (0,b) and (a,0), with each remote delay between one and k. The history length K independently bounds both delays and includes all slots from zero through K.

The nonzero spectrum correspondence is used in both directions. Its zero-delay, one-slot specialization identifies the synchronous spectrum with the square roots of the product spectrum. For the upper bound, a delayed spectral value gives a product spectral value and then a synchronous spectral value. For equality, a synchronous spectral value of maximal modulus gives a product value whose complex roots lift back to the actual delayed matrix. No positive real eigenvalue, sign condition, rank condition, or equality of the two block sizes is required.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousTwoBlockRadius.two_block_radius`
- Dependency: [D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum](AsynchronousTwoBlockSpectrum.md)
