# Fixed external coefficients of the original sewn Gaussian

## Abstract

OriginalGaussianFixedExternalCoefficient

The actual mixed occupation summands are differentiated in both external families at their full degrees. Summable Cauchy bounds on each fixed-cutoff source germ justify extraction through the occupation sum. The resulting terms are the literal full native rows, including the full opposite-charge inverse colour transport and exactly one internal factorial. Their source powers are twice the internal energy. Local uniform source differentiation then identifies the finite sewn coefficient with the finite energy layer. The fixed-cutoff normal germ is distinct from the common holomorphic domain used for the explicit sewn cutoff limit. No uniform lower bound for occupation radii is used. Empty supports, rank zero, cutoff zero and energy zero remain included.

**Definition 1.1 (Actual full sewn row summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.fullRowTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.fullRowTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The damped full row coefficients retain all external degrees and one internal factorial.

**Definition 1.2 (Undamped original full rows).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.rawFullRowTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.rawFullRowTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right row uses the complete inverse colour transport of the original opposite-charge mean.

**Theorem 1.3 (Normally sewn full external occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_fixed_external_sewing_on_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_fixed_external_sewing_on_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two ordinary external extractions pass through the actual normally convergent occupation sum. The resulting uniform majorant belongs only to one positive fixed-cutoff germ.

**Theorem 1.4 (Finite sewn ordinary energy coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_finiteSewn_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_finiteSewn_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After justified external extraction and source differentiation, the coefficient of order twice the energy, divided by its full factorial, is exactly the original native full-row energy layer.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.fullRowTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_finiteSewn_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.original_fixed_external_sewing_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.rawFullRowTerm`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient](NativeAffineExternalCoefficient.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction](OriginalGaussianSourceRestriction.md)
