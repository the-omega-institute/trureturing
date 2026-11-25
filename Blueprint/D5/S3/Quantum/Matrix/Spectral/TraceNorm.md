# The matrix trace norm and Hermitian Jordan mass

## Abstract

The matrix trace norm and Hermitian Jordan mass

RCLike is the real-or-complex scalar interface. FiniteType denotes a finite coordinate type with decidable equality; FintypeType assumes finiteness alone. ReTr is the real part of the unnormalized trace; square roots, positive parts and negative parts use the spectral matrix calculus. The rectangular trace-norm definition is the attributed Physlib definition, and the Hermitian identity uses the canonical spectral positive and negative parts.

**Definition 1.1 (The actual rectangular trace norm).**

$$\forall m \in FintypeType, n \in FintypeType, k \in RCLike, A \in \operatorname{Matrix}\left(m, n, k\right),\; \operatorname{traceNorm}\left(A\right) = \operatorname{ReTr}\left(\operatorname{sqrt}\left(A^{*} \cdot A\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/Spectral/TraceNorm.traceNorm` (`✓ std3`).

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

For any finite row and column types and any RCLike scalar type, traceNorm(A) is ReTr(sqrt(A* A)). Only finiteness is required by this definition; no decidable equality, square shape, normalization or invertibility is assumed.

**Theorem 1.2 (The positive and negative masses add).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; (\operatorname{IsHermitian}\left(A\right)) \Rightarrow (\operatorname{traceNorm}\left(A\right) = \operatorname{ReTr}\left(\operatorname{posPart}\left(A\right)\right) + \operatorname{ReTr}\left(\operatorname{negPart}\left(A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/TraceNorm.trace_norm_jordan_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian complex square matrix A on a finite decidable coordinate type, traceNorm(A)=ReTr(posPart(A))+ReTr(negPart(A)). Spectral absolute value equals the sum of these two positive parts, and its trace is the trace norm. The identity includes singular matrices and the empty type.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/TraceNorm.traceNorm`
- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/TraceNorm.trace_norm_jordan_mass`
