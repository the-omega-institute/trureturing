# Original source contraction germs and trace similarity

## Abstract

OriginalGaussianSourceGerm

For a fixed frequency cutoff, both actual internal source matrices vanish at zero. The right matrix contains every retained colour in its original inverse substitution. Entrywise positive comparisons vanish there as well. Finite dimensional continuity gives one positive closed contraction disk for these four matrices. Its radius may depend on the cutoff; no uniform occupation majorant or convergence on the unit disk is asserted.

The raw product is diagonally similar to the colour identity tensored with the square of the normalized finite section. Cyclicity of trace removes the positive frequency diagonal at every power, including power zero. Thus the arbitrary-mean finite sewing trace exponential is exactly exp(-(rank/2)*finiteLog). This algebraic identity needs no inverse of the sewing variable and includes empty mode or colour types. The source energy coefficient identity still needs analytic extraction and source stabilization.

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

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.left_entry_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_contract_on_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_power`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.original_rows_trace_prefactor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.positiveInternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.right_entry_differentiable`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteAffineGaussianSewing](FiniteAffineGaussianSewing.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans](OriginalGaussianSourceMeans.md)
