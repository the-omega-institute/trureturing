# InfiniteGaussianSewing

## Abstract

InfiniteGaussianSewing

Finite Gaussian sewing extends to arbitrary internal mode types by absolute convergence and a common finite-subset limit. The effective kernel retains the ordered inverses of BA and AB and the trace-log normalization of AB.

**Theorem 1.1 (Exact finite coefficient stabilization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.coefficient_finite_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.coefficient_finite_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any finite injective set of coordinates computes the same actual coefficient as its zero extension. The proof uses the existing coefficient_on_block and gaussianCoefficient_enlarge theorems on the actual finite image, including all repeated occupations.

**Theorem 1.2 (Finite sewing on coordinate supports).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoff_sewing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoff_sewing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex every occupation supported in F through the actual restriction and extension equivalence. Apply FiniteGaussianSewing.finite_sewing to the exact principal blocks and mixed coordinate restrictions. The scalar is identified with the true traceLog(cutoffProduct A B F) by the positive-power trace identity.

**Theorem 1.3 (The three effective block limits).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoffKernel_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoffKernel_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N=(1-BA)^-1 and V=(1-AB)^-1. The diagonal effective entries tend to P+R N B R^t and Q+S^t V A S. The finite mixed entry is R N_F S-R(1-P_F)S, and therefore tends to R N S. Matrix transpose algebra identifies the opposite mixed block with its bilinear coordinate transpose. The argument uses the same finite-subset net as the actual occupation cutoffs.

**Theorem 1.4 (Complete infinite external Gaussian sewing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.sewing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.sewing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary internal index I, finite X,Y, transpose-symmetric Hilbert-Schmidt strict contractions A,B, arbitrary finite symmetric P,Q and arbitrary finite families of l2 mixed rows R_x and columns S_y, the actual coefficient contraction is absolutely summable for every d,e and equals exp(traceLog(AB)) times the ordinary Gaussian coefficient of the ordered effective kernel. The first source kernel is [[P,R],[R^t,A]] on X+I and the second is [[B,S],[S^t,Q]] on I+Y. The proof applies the actual finite identity at every F, proves both genuine limits and uses uniqueness. The trace-log is the positive-power series of the original trace-class product AB, not a cutoff-defined trace. Empty I gives c_P(d)c_Q(e) with normalization one, rather than generally one. This is classical Gaussian/Fock sewing, not a claim of a completed VOA, string theory or AdS/CFT construction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.coefficient_finite_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoffKernel_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.cutoff_sewing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.sewing`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing](FiniteGaussianSewing.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity](GaussianCoefficientContinuity.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianSewingLimit](GaussianSewingLimit.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows](InfiniteGaussianRows.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianVacuum](InfiniteGaussianVacuum.md)
