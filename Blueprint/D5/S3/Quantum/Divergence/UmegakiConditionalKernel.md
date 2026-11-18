# Matrix coordinates of the arithmetic inverse

## Abstract

Inverse and energy identities used in the faithful conditional Umegaki estimate.

**Definition 1.1 (Arithmetic interpolation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite square complex matrices Z and X and real u, this is (1-u) ZX + u XZ in the original matrix coordinates.

**Definition 1.2 (Coordinates of the native inverse).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport V to the Hilbert–Schmidt carrier, apply the continuous-linear-map inverse of the native arithmetic operator at Z and u, and transport back. The cancellation laws below supply invertibility under their stated hypotheses.

**Definition 1.3 (Native inverse quadratic form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real part of the Hilbert–Schmidt pairing of V with its image under the same native inverse.

**Definition 1.4 (Arithmetic energy).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy of X is the real trace of X adjoint times arithmetic(Z,X,u).

**Theorem 1.5 (Integrability of the inverse pairing).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverse_pairing_intervalIntegrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverse_pairing_intervalIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite square complex Z and H with Z positive definite, the real inverse pairing of H is interval integrable on [0,1]. The finite spectral expansion and the integrable affine reciprocal terms justify the integration in the conditional BKM estimate.

**Theorem 1.6 (Left inverse cancellation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverseMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverseMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Z is positive definite and u lies in [0,1], applying arithmetic at Z to inverseMatrix(Z,V,u) recovers the arbitrary complex V. This cancels the marginal inverse in the residual and identifies the output inverse direction in the kernel estimate.

**Theorem 1.7 (Right inverse cancellation).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positivity and interval hypotheses, inverseMatrix applied to arithmetic(Z,X,u) recovers X. This supplies the endpoint computation.

**Theorem 1.8 (Trace of the inverse form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Z, V and real u, q is the real trace of V adjoint times inverseMatrix(Z,V,u). The identity uses the native trace pairing and also applies where the inverse is totalized. The residual computation uses this trace identity.

**Theorem 1.9 (The ordinary inverse at the left endpoint).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_zero_parameter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_zero_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and arbitrary complex V, q(Z,V,0) equals Re Tr(V adjoint Z inverse V). The kernel proof substitutes this equality for the input direction constructed from the reference center.

**Theorem 1.10 (Nonnegative arithmetic energy).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive semidefinite Z and u in [0,1], the energy of any complex X is nonnegative. The endpoint trace test and inverse nonnegativity use this bound.

**Theorem 1.11 (Energy of the inverse direction).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_energy_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_energy_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and u in [0,1], q(Z,V,u) is the energy of inverseMatrix(Z,V,u). The residual, weighted Cauchy–Schwarz, and kernel proofs use this equality.

**Theorem 1.12 (Nonnegative inverse form).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and u in [0,1], q is nonnegative for any complex V. The kernel proof applies this to both input and output before handling zero and positive cases.

**Theorem 1.13 (Weighted Cauchy–Schwarz).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.weighted_cauchy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.weighted_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z, u in [0,1], and arbitrary complex matrices X and V, the square of Re Tr(X adjoint V) is at most energy(Z,X,u) times q(Z,V,u). The kernel proof uses the same inequality with the centered and uncentered adjoints.

**Theorem 1.14 (Expansion after subtracting an arithmetic image).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_sub_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_sub_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z, u in [0,1], and arbitrary complex H and X, the inverse form of H minus arithmetic(Z,X,u) equals q(Z,H,u) minus twice Re Tr(X adjoint H) plus energy(Z,X,u). This is the expansion used in the joint-minus-marginal residual identity.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverseMatrix`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.arithmetic_inverse_pairing_intervalIntegrable`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.energy_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.inverseMatrix_arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_energy_inverse`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_eq_trace`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_sub_arithmetic`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.q_zero_parameter`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiConditionalKernel.weighted_cauchy`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiArithmeticBKM](UmegakiArithmeticBKM.md)
