# PsdThreeCubicComplex

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Definition 1.1 (Mat).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.Mat`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing Mathlib matrix carrier specialized to complex three by three matrices.

**Definition 1.2 (cycle).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cycle`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual oriented complex product S01 S12 S20.

**Definition 1.3 (matrixPair).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.matrixPair`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.matrixPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three weighted pair terms use the original source diagonal real parts and squared complex entry norms. They are nonnegative for a PSD source and nonnegative weights.

**Definition 1.4 (cubic).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weighted matrix pair energy plus k times the real part of the oriented source cycle.

**Theorem 1.5 (negative cycle gram).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.negative_cycle_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.negative_cycle_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex PSD matrix, positive x,y with normSq(S01)=x^2 and normSq(S12)=y^2, and real z with Re(S01 S12 S20)=-xyz, the explicitly scaled vector (xyu,-conj(S01)yv,conj(S01 S12)w) gives a nonnegative real quadratic form with the same three diagonal entries. No sign restriction on z, rank, inverse or external diagonal frame is assumed.

**Theorem 1.6 (cubic nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex PSD three by three matrix has nonnegative cubic whenever a,b,c,k are nonnegative and k <= allowance(a,b,c). This includes singular matrices, arbitrary phases and zero weights; the coefficient hypotheses require an independent application-specific proof.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.Mat`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cubic_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.cycle`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.matrixPair`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubicComplex.negative_cycle_gram`
- Dependency: [D5/S3/Quantum/Matrix/PsdThreeCubic](PsdThreeCubic.md)
