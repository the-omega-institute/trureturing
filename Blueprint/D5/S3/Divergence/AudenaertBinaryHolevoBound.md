# Audenaert's binary Holevo bound

## Abstract

Binary Holevo information in bits is at most half the trace norm of the difference.

**Theorem 1.1 (The binary ensemble inequality).**

$$\forall (n: \mathbb{N}), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (tau: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{PosSemidef}\left(sigma\right)) \land (\operatorname{trace}\left(sigma\right) = 1)) \Rightarrow (((\operatorname{PosSemidef}\left(tau\right)) \land (\operatorname{trace}\left(tau\right) = 1)) \Rightarrow (- \operatorname{re}\left(\operatorname{trace}\left(\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x \cdot \operatorname{Real}.\operatorname{logb} (2, x)), (\frac{1}{2}: \mathbb{C}) \cdot (sigma + tau)\right)\right)\right) - \frac{- \operatorname{re}\left(\operatorname{trace}\left(\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x \cdot \operatorname{Real}.\operatorname{logb} (2, x)), sigma\right)\right)\right) + - \operatorname{re}\left(\operatorname{trace}\left(\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x \cdot \operatorname{Real}.\operatorname{logb} (2, x)), tau\right)\right)\right)}{2} \le \frac{\operatorname{traceNorm}\left(sigma - tau\right)}{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/AudenaertBinaryHolevoBound.binaryHolevoBound` (`✓ std3`). ∎

*Citation.* Koenraad M. R. Audenaert (2014). *Quantum Skew Divergence*. DOI: [10.1063/1.4901039](https://doi.org/10.1063/1.4901039). URL: <https://arxiv.org/abs/1304.5935v2>.

*Commentary.*

Audenaert, Quantum Skew Divergence, Theorem 14, bounds Holevo information by the classical mixing entropy times the maximal trace distance. For an equiprobable binary ensemble the mixing entropy is one bit. The matrices may be singular. The matrix-log resolvent integral gives the derivative along a positive affine path. Positivity of that derivative and its trace pairing bound the skew divergence by trace distance times the negative logarithm of the mixing weight. Specializing the weight to one half gives the binary inequality for strictly positive states. Adding epsilon times the identity and dividing by one plus n epsilon preserves trace one, and continuity of x log x extends the estimate to singular states.

## References

- Truth anchor: `D5/S3/Divergence/AudenaertBinaryHolevoBound.binaryHolevoBound`
- Dependency: [D5/S3/ArithSums/TwoPointSlabSupport](../ArithSums/TwoPointSlabSupport.md)
- Dependency: [D5/S3/Divergence/LogDerivTrace](LogDerivTrace.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Quantum/Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](../Quantum/Subentropy/UniformIntegrals.md)
