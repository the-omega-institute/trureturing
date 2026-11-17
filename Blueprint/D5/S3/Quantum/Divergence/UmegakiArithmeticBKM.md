# Native arithmetic inverse and the BKM form

## Abstract

The actual Bochner logarithmic derivative equals the integrated native Hilbert-Schmidt arithmetic inverse pairing.

**Definition 1.1 (The native arithmetic map).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex matrix Z on any finite index type, transport Z by Matrix.toEuclideanCLM. On the existing HilbertSchmidtOperatorSpace.HSOp carrier, M_Z(u) is (1-u) times left multiplication by Z plus u times right multiplication by Z. No second Hilbert-Schmidt carrier or common input/output eigenbasis is introduced.

**Theorem 1.2 (The arbitrary-complex Bochner identity).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type iota, positive definite complex Z, and arbitrary complex H, Re Tr(H adjoint times LogDerivTrace.logDeriv(Z,H)) equals the integral from zero to one of Re inner(H, inverse(M_Z(u)) H), using the native matrix-to-HS transport. H is not required to be Hermitian, to commute with Z, or to have any trace or normalization. Empty index types and repeated eigenvalues are included.

Diagonalize Z alone as U diag(lambda) U adjoint. The explicit matrix candidate Q_u(H)=U [D_u entrywise-multiplied by (U adjoint H U)] U adjoint uses D_u(i,j)=1/((1-u)lambda_i+u lambda_j). Each denominator is strictly positive on the closed interval, including both endpoints. The verified composition M_Z(u) Q_u=id and finite-dimensional linear equivalence give an actual continuous inverse; only then is the total ContinuousLinearMap.inverse rewritten. The equivalence Matrix.toEuclideanLin followed by hsLinearMapEquiv inverse works uniformly for empty carriers.

The native HS inner product becomes the actual matrix trace. Both pairings expand as finite sums of squared complex entry norms times scalar kernels. LogDerivTrace.logDeriv_integrable justifies commuting the fixed real trace map with the Bochner integral; pairKernel_integrable and affine interval integrability justify every finite-sum interchange. The original UmegakiRareFlagBKM.pair_kernel_eval and trace_cross_spectral are exposed and directly consumed, preserving their proofs and the rare-flag theorem. Equal eigenvalues use the reciprocal branch; no unguarded division by an eigenvalue difference occurs.

The identity is a repository-derived support result for the same conditional Umegaki problem, not a novelty or coefficient-equality claim. The full correlated bipartite quantum consumer must apply the ordinary UmegakiBKMPath.relativeEntropy_eq_integral_bkm separately to the joint and actual partial-trace marginal matrices, cancel trace corrections with trace_partialTraceRight, and use the actual HS partial-trace residual. The finite nonempty block-family conditional theorem supplies a classical-label case only. The original all-finite contraction-coefficient chain remains unproved, with open-problem KPI zero.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace](../Lieb/HilbertSchmidtOperatorSpace.md)
