# Signed Generators of the Literal Source Amplitudes

## Abstract

Signed Generators of the Literal Source Amplitudes

Absolute reindexing sums the actual A coefficients over the external modes. The positive generator is (1-u)^(-1) times the central binomial series at -xu/(1-u); the negative generator uses x/(1-u). The binomial power series fixes the analytic branches at the origin. The all-mode J/T kernel identification, removable J diagonal and singular-ODE coefficient uniqueness remain separate unproved obligations.

**Definition 1.1 (centralGenerating).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.centralGenerating`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.centralGenerating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the literal centralWeight power series in a complex argument.

**Theorem 1.2 (sourceAmplitude_mode_hasSum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign and norm(u)+norm(x)<1, the complete A mode sum has the value obtained by summing its absolutely convergent coefficient double series in the reversed order.

**Theorem 1.3 (sourceAmplitude_positive_generator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On norm(u)+norm(x)<1, the positive A mode series sums to centralGenerating(-xu/(1-u))/(1-u).

**Theorem 1.4 (sourceAmplitude_negative_generator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On norm(u)+norm(x)<1, the negative A mode series sums to centralGenerating(x/(1-u))/(1-u).

**Theorem 1.5 (sourceAmplitude_generators).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_generators`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On norm(u)+norm(x)<1, both complete signed A mode series equal their analytic binomial branches: positive (1-u)^(-1)(1+xu/(1-u))^(-1/2), negative (1-u)^(-1)(1-x/(1-u))^(-1/2). No value of a singular J quotient is assigned at the diagonal.

**Definition 1.6 (sourceMode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either sign and complex u,x, sourceMode is the tsum of the actual sourceAmplitude at each natural external mode times u to that mode.

**Theorem 1.7 (sourceMode_square).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On norm(u)+norm(x)<1, the actual positive sourceMode square is 1/((1-u)(1-(1-x)u)); the negative square is 1/((1-u)(1-x-u)). The previously evaluated binomial branches fix which square root germ occurs.

**Definition 1.8 (amplitudeTerm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.amplitudeTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.amplitudeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either label and complex u,x, this is the actual coefficient product c_n (-1)^n choose(alpha(p)-1/2,n) x^n u^p on the pair (p,n). It is consumed by the absolute mode-reindexing theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.amplitudeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.centralGenerating`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_generators`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode_square`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal](OriginalGaussianExternalNormal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalSourceJet](OriginalGaussianExternalSourceJet.md)
