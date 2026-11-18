# Endpoint contraction on the partial-trace kernel

## Abstract

A uniform endpoint estimate implies the arithmetic inverse-form estimate at every parameter.

**Definition 1.1 (Arithmetic interpolation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite square complex matrices Z and X and real u, this is (1-u) ZX + u XZ in the original matrix coordinates.

**Definition 1.2 (Coordinates of the native inverse).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport V to the Hilbert–Schmidt carrier, apply the continuous-linear-map inverse of the native arithmetic operator at Z and u, and transport back. The cancellation laws below supply invertibility under their stated hypotheses.

**Definition 1.3 (Native inverse quadratic form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real part of the Hilbert–Schmidt pairing of V with its image under the same native inverse.

**Definition 1.4 (Arithmetic energy).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy of X is the real trace of X adjoint times arithmetic(Z,X,u).

**Theorem 1.5 (Left inverse cancellation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic_inverseMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic_inverseMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Z is positive definite and u lies in [0,1], applying arithmetic at Z to inverseMatrix(Z,V,u) recovers the arbitrary complex V. This cancels the marginal inverse in the residual and identifies the output inverse direction in the kernel estimate.

**Theorem 1.6 (Right inverse cancellation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positivity and interval hypotheses, inverseMatrix applied to arithmetic(Z,X,u) recovers X. This supplies the endpoint computation.

**Theorem 1.7 (Trace of the inverse form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Z, V and real u, q is the real trace of V adjoint times inverseMatrix(Z,V,u). The identity uses the native trace pairing and also applies where the inverse is totalized. The residual computation uses this trace identity.

**Theorem 1.8 (The ordinary inverse at the left endpoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_zero_parameter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_zero_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and arbitrary complex V, q(Z,V,0) equals Re Tr(V adjoint Z inverse V). The kernel proof substitutes this equality for the input direction constructed from the reference center.

**Theorem 1.9 (Nonnegative arithmetic energy).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive semidefinite Z and u in [0,1], the energy of any complex X is nonnegative. The endpoint trace test and inverse nonnegativity use this bound.

**Theorem 1.10 (Energy of the inverse direction).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_energy_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_energy_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and u in [0,1], q(Z,V,u) is the energy of inverseMatrix(Z,V,u). The residual, weighted Cauchy–Schwarz, and kernel proofs use this equality.

**Theorem 1.11 (Nonnegative inverse form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and u in [0,1], q is nonnegative for any complex V. The kernel proof applies this to both input and output before handling zero and positive cases.

**Theorem 1.12 (Weighted Cauchy–Schwarz).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.weighted_cauchy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.weighted_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z, u in [0,1], and arbitrary complex matrices X and V, the square of Re Tr(X adjoint V) is at most energy(Z,X,u) times q(Z,V,u). The kernel proof uses the same inequality with the centered and uncentered adjoints.

**Theorem 1.13 (Expansion after subtracting an arithmetic image).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_sub_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_sub_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z, u in [0,1], and arbitrary complex H and X, the inverse form of H minus arithmetic(Z,X,u) equals q(Z,H,u) minus twice Re Tr(X adjoint H) plus energy(Z,X,u). This is the expansion used in the joint-minus-marginal residual identity.

**Theorem 1.14 (Faithfulness under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z on a finite reference times a nonempty finite local carrier, the ordinary partial trace is positive definite. It is the sum of positive definite principal blocks. The reference center, residual identity and faithful state pairs use this fact.

**Theorem 1.15 (Right reference multiplication under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_mul_embed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_mul_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex matrices Z and X, the partial trace of Z times X tensor I is P(Z) times X. This puts the endpoint direction in the kernel and transports the marginal arithmetic operator.

**Theorem 1.16 (Left reference multiplication under partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_embed_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_embed_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partial trace of (X tensor I) times Z is X times P(Z). This supplies the trace pairing and the left part of the marginal arithmetic operator.

**Theorem 1.17 (Complex trace adjunction).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.trace_embed_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.trace_embed_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tr((X tensor I) adjoint V) equals Tr(X adjoint P(V)) for arbitrary complex matrices, using the ordinary partial trace. This preserves the pairing on zero-partial-trace directions when the reference center is subtracted.

**Theorem 1.18 (Amplification on an elementary tensor).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_kronecker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite channel N and arbitrary complex X and Z on the reference and input, the amplification sends X tensor Z to X tensor N(Z). This computes the channel image of the identity in the positivity argument.

**Theorem 1.19 (Amplification preserves matrix order).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the canonical finite channel, input matrix order X ≤ Z implies the same order for their amplified images. This transports a strictly positive lower bound.

**Theorem 1.20 (Positive lower bound by the identity).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.positive_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.positive_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive definite complex matrix on a finite carrier dominates m times the identity for some real m > 0. On the empty carrier the proof chooses m = 1. Amplification uses this lower bound.

**Theorem 1.21 (Faithfulness under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If N(I) is positive definite, the amplified channel sends each positive definite joint Z to a positive definite matrix for every finite reference. The assertion includes correlated input and the empty reference. The inverse-form and density-state proofs use this implication.

**Theorem 1.22 (Right reference multiplication under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mul_embed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mul_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplification of Z times X tensor input identity equals the amplification of Z times X tensor output identity. The reference center and the output residual use this law on arbitrary complex matrices.

**Theorem 1.23 (Left reference multiplication under amplification).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_embed_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_embed_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The amplification of (X tensor input identity) times Z equals (X tensor output identity) times the amplification of Z. This supplies the other multiplication law for the output residual.

**Theorem 1.24 (Bilinear trace pairing of the channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_trace_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_trace_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty input and output, every finite reference and arbitrary complex Y and Z, Tr(PhiR(Y) Z) equals Tr(Y amp(N,Z)). The canonical Kraus adjoint is paired with the actual channel action. This gives the channel energy defect and the conjugate-transpose pairing.

**Theorem 1.25 (Hilbert–Schmidt pairing of the channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_hs_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_hs_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same carrier hypotheses, Tr(PhiR(Y) adjoint Z) equals Tr(Y adjoint amp(N,Z)). This pairs the chosen output inverse direction and its reference-centered form with the original input direction.

**Definition 1.26 (The uniform left-endpoint premise).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a canonical finite channel N and coefficient c, quantify over every finite reference and every pair Z,V of complex joint matrices with Z positive definite and ordinary partial trace of V zero. The amplified left-endpoint inverse form is at most c times the input form. The inverse at zero pairs V with Z inverse V.

**Theorem 1.27 (Arithmetic inverse contraction on the kernel).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a canonical finite channel between nonempty carriers with N(I) positive definite. Let 0 ≤ c ≤ 1 and assume EndpointBound(N,c). For every finite reference, correlated positive definite Z, complex V with zero ordinary partial trace, and u in [0,1], q(amp(N,Z),amp(N,V),u) ≤ c q(Z,V,u). The reference may be empty.

For c < 1, take the endpoint reference center X = (PZ) inverse P(Z PhiR(Y)). The direction Z times (PhiR(Y) minus X tensor I) has zero partial trace. The endpoint inequality and weighted Cauchy–Schwarz bound the centered energy by k times the channel defect, where k = c/(1-c). This gives a universal trace test for the common-state scalarizer.

The scalarizer supplies one state and both residual Gram bounds. With p the input inverse form, q the output inverse form, f the uncentered input energy and d = q-f, the two pairings bound q squared by f p and k d p. For q > 0 their combination yields (1+k)q ≤ k p. The proof handles q = 0 before cancellation, includes c = 0, and at c = 1 uses the uncentered bound and d ≥ 0.

This estimate is used on the actual joint-minus-marginal residual in the faithful density-state theorem. The premise still requires a uniform endpoint bound for all references and complex kernel directions. The coefficient equality for all supported pairs and all channels remains open.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_hs_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.PhiR_trace_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_embed_mul`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_kronecker`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mono`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_mul_embed`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.amp_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.arithmetic_inverseMatrix`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.energy_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.inverseMatrix_arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_embed_mul`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_mul_embed`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.partialTraceRight_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.positive_floor`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_energy_inverse`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_eq_trace`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_sub_arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.q_zero_parameter`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.trace_embed_pair`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.weighted_cauchy`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiArithmeticBKM](UmegakiArithmeticBKM.md)
- Dependency: [D5/S3/Quantum/Divergence/UniversalPositiveScalarizer](UniversalPositiveScalarizer.md)
