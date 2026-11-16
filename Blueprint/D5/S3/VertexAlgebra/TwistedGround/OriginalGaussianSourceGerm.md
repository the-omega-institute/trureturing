# Original source contraction germs and trace similarity

## Abstract

OriginalGaussianSourceGerm

For a fixed frequency cutoff, both actual internal source matrices vanish at zero. The right matrix contains every retained colour in its original inverse substitution. Entrywise positive comparisons vanish there as well. Finite dimensional continuity gives one positive closed contraction disk for these four matrices. Its radius may depend on the cutoff; the resulting occupation majorant is fixed only at this cutoff, and no convergence on the unit disk is asserted.

The raw product is diagonally similar to the colour identity tensored with the square of the normalized finite section. Cyclicity of trace removes the positive frequency diagonal at every power, including power zero. Thus the arbitrary-mean finite sewing trace exponential is exactly exp(-(rank/2)*finiteLog). This algebraic identity needs no inverse of the sewing variable and includes empty mode or colour types. The native coefficient comparison proves a summable majorant uniformly over the closed source germ and both external unit polydisks. It controls the actual mixed means and exponentials. Exact diagonal scaling retains twice the internal occupation energy. Finite arbitrary-mean sewing holds before external extraction. The source energy layer stabilizes by full-colour box restriction; external analytic coefficient extraction remains separate.

**Definition 1.1 (Positive internal comparison).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.positiveInternal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.positiveInternal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take each undamped internal entry's norm and multiply by the two nonnegative radius powers at its positive frequencies. The complete inverse colour transport precedes this comparison.

**Theorem 1.2 (Polynomial left entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.left_entry_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.left_entry_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual damped left entry is a polynomial in the source variable.

**Theorem 1.3 (Polynomial fully transported right entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.right_entry_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.right_entry_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse transport is independent of the source variable, and damping makes each actual right entry a polynomial.

**Theorem 1.4 (A common fixed-cutoff contraction germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_contract_on_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_contract_on_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite intersection of strict norm neighbourhoods contains a positive closed disk. Both raw internal matrices and both positive comparisons are strict Euclidean contractions throughout it. No positive-rank or nonempty-support assumption occurs.

**Theorem 1.5 (Literal raw trace similarity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_power`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative power p the raw internal product trace is rank times trace(finiteSection to the power 2*p). The proof retains the complete inverse Gram transport and both positive frequency diagonals.

**Theorem 1.6 (Exact finite sewing normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_prefactor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_prefactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace-power identity and scalar linearity of the trace series give exp(-(rank/2)*finiteLog). No charge average or extra overall factor is introduced.

**Definition 1.7 (Actual mixed mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.mixedMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.mixedMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original internal mean plus the finite original internal-to-external couplings evaluated at the retained external coordinates.

**Definition 1.8 (Original external exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.externalExponent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.externalExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One half of the ordinary external quadratic sum plus the original external linear sum, without conjugation.

**Definition 1.9 (Undamped original mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original corrected mean is restricted to the full internal colour-frequency box and the given external labels.

**Definition 1.10 (Fully transported opposite-charge mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalInverseMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalInverseMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the complete inverse colour substitution to the original mean at charge minus a before any frequency restriction.

**Definition 1.11 (Literal mixed occupation term).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.occupationTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.occupationTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two actual affine coefficients are multiplied by one internal factorial and both original external exponentials.

**Definition 1.12 (Fixed-cutoff source domain).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.sourcePolydisk`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.sourcePolydisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A closed source disk times the two external unit polydisks, including empty external families.

**Theorem 1.13 (Literal raw right mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rightMean_raw`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rightMean_raw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual damped opposite-charge mean is the damping times its complete original inverse-colour transport. This interface is consumed by the nested-box coefficient restriction proof.

**Theorem 1.14 (Uniform summable occupation majorant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_majorant_on_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_majorant_on_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficientwise finite polynomial comparison dominates the actual covariances and mixed means by symmetric nonnegative arrays at one fixed radius. The accepted affine factorial-square summability supplies a single summable bound independent of the source and external points.

**Theorem 1.15 (Normal convergence before extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_normal_on_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_normal_on_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The summable majorant yields uniform convergence of all finite occupation partial sums on the closed fixed-cutoff source polydisk.

**Definition 1.16 (Positive internal energy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.internalEnergy`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.internalEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum frequency times occupation over the full internal support, with positive frequencies starting at one.

**Theorem 1.17 (Exact full-row energy scaling).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_coefficients_scale`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_coefficients_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both literal affine row coefficients scale by the source power at their internal energy. Each full native row degree retains its external occupation.

**Theorem 1.18 (Twice the internal energy).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_product_scales`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_product_scales` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product has exactly one internal factorial and exactly the source power twice its internal energy, also at zero energy.

**Definition 1.19 (Undamped mixed source expression).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rawOccupationTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rawOccupationTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The algebraic expression retains both original means, the transported right covariance and both external coordinate families; no summability at source value one is asserted.

**Theorem 1.20 (Mixed-source energy scaling).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_scales`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_scales` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mixed mean scales with its internal frequency, while the external exponent stays fixed. Diagonal Gaussian congruence gives exactly twice the occupation energy.

**Definition 1.21 (Uncollected finite sewn exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.finiteMixedExponent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.finiteMixedExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both original external exponents plus the ordered effective quadratic expression in the two actual mixed means.

**Theorem 1.22 (Actual row symmetry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_symm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual damped covariances are symmetric under ordinary transpose. Complete inverse transport preserves the original covariance symmetry before damping.

**Theorem 1.23 (Literal finite mixed-mean sewing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_sewing_on_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_sewing_on_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One common fixed-cutoff germ supports normal convergence and the exact arbitrary-mean sewing equality. Its determinant factor is exp(-(rank/2)*finiteLog), with no inverse of the source variable.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.externalExponent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.finiteMixedExponent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.internalEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.left_entry_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.mixedMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.occupationTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalInverseMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.originalMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_majorant_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_normal_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_scales`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_occupation_sewing_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_coefficients_scale`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_row_product_scales`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_contract_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_symm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_power`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_prefactor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.positiveInternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rawOccupationTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.rightMean_raw`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.right_entry_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.sourcePolydisk`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteAffineGaussianSewing](FiniteAffineGaussianSewing.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans](OriginalGaussianSourceMeans.md)
