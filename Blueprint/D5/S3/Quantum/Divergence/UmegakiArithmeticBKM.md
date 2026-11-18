# Native arithmetic inverse and the BKM form

## Abstract

The actual Bochner logarithmic derivative equals the integrated native Hilbert-Schmidt arithmetic inverse pairing.

**Definition 1.1 (The native arithmetic map).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex matrix Z on any finite index type, transport Z by Matrix.toEuclideanCLM. On the existing HilbertSchmidtOperatorSpace.HSOp carrier, M_Z(u) is (1-u) times left multiplication by Z plus u times right multiplication by Z. No second Hilbert-Schmidt carrier or common input/output eigenbasis is introduced.

**Definition 1.2 (Native matrix-to-Hilbert–Schmidt equivalence).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.matrixHS`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.matrixHS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite carrier, matrix-to-Euclidean linear transport composed with the inverse of hsLinearMapEquiv gives the complex linear equivalence used by the arithmetic inverse coordinates.

**Theorem 1.3 (Arithmetic action in matrix coordinates).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex Z and X and real u, the native map on matrixHS(X) is matrixHS((1-u) ZX + u XZ). This gives the arithmetic inverse cancellations and the energy computation.

**Theorem 1.4 (Invertibility on the closed arithmetic interval).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap_isInvertible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap_isInvertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z and u in [0,1], the native arithmetic map is invertible. This justifies use of the total continuous-linear inverse in both matrix cancellation directions.

**Theorem 1.5 (Integrable affine reciprocal).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.affineKernel_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.affineKernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real a and b, the reciprocal of (1-u)a+ub is interval integrable on [0,1]. Applying this to the eigenvalue pairs supplies integrability of the arbitrary complex inverse pairing.

**Theorem 1.6 (The native Hilbert–Schmidt trace pairing).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsInner_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsInner_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert–Schmidt inner product of the operator of X with matrixHS(Y) equals Tr(X adjoint Y) for arbitrary finite complex matrices. The trace and inverse energy identities use this pairing.

**Theorem 1.7 (Spectral expansion of the real inverse pairing).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hs_pair_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hs_pair_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite Z, arbitrary complex H and u in [0,1], the real native inverse pairing is the finite sum over eigenvalue pairs of squared norms of the entries of H in the eigenbasis, times the reciprocal of the arithmetic eigenvalue interpolation. The inverse-pairing integrability proof uses this finite sum.

**Theorem 1.8 (The arbitrary-complex Bochner identity).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type iota, positive definite complex Z, and arbitrary complex H, Re Tr(H adjoint times LogDerivTrace.logDeriv(Z,H)) equals the integral from zero to one of Re inner(H, inverse(M_Z(u)) H), using the native matrix-to-HS transport. H is not required to be Hermitian, to commute with Z, or to have any trace or normalization. Empty index types and repeated eigenvalues are included.

Diagonalize Z alone as U diag(lambda) U adjoint. The explicit matrix candidate Q_u(H)=U [D_u entrywise-multiplied by (U adjoint H U)] U adjoint uses D_u(i,j)=1/((1-u)lambda_i+u lambda_j). Each denominator is strictly positive on the closed interval, including both endpoints. The verified composition M_Z(u) Q_u=id and finite-dimensional linear equivalence give an actual continuous inverse; only then is the total ContinuousLinearMap.inverse rewritten. The equivalence Matrix.toEuclideanLin followed by hsLinearMapEquiv inverse works uniformly for empty carriers.

The native HS inner product becomes the actual matrix trace. Both pairings expand as finite sums of squared complex entry norms times scalar kernels. LogDerivTrace.logDeriv_integrable justifies commuting the fixed real trace map with the Bochner integral; pairKernel_integrable and affine interval integrability justify every finite-sum interchange. The original UmegakiRareFlagBKM.pair_kernel_eval and trace_cross_spectral are exposed and directly consumed, preserving their proofs and the rare-flag theorem. Equal eigenvalues use the reciprocal branch; no unguarded division by an eigenvalue difference occurs.

The following derivation starts from a bound at every arithmetic parameter. UmegakiKernelContraction now derives that bound from the uniform left-endpoint premise, and UmegakiConditionalBKM owns the resulting faithful density-state implication.

A faithful conditional application uses the canonical FiniteStateChannel.QuantumChannel N and its actual FiniteDiamondDistance.referenceAction T. Write P=partialTraceRight, Pstar(K)=K tensor I, and q(Z,V,u)=Re inner(HS(V),inverse(M_Z(u)) HS(V)). Suppose c is nonnegative and, for every finite reference R, every u in [0,1], every complex V with PV=0, and every positive definite Z whose TZ is positive definite, q(TZ,TV,u) is at most c q(Z,V,u). For canonical density states rho and sigma with rho, sigma, T rho and T sigma positive definite, this implies D_fin(T rho,T sigma)-D_fin(rho_R,sigma_R) is at most c times [D_fin(rho,sigma)-D_fin(rho_R,sigma_R)]. Here D_fin is SupportAwareRelativeEntropy.finiteTraceLogRelativeEntropy, and rho_R and sigma_R are the actual marginalRight states transported through the existing LegacyRelativeEntropyBoundary adapters. The matrix and CStarMatrix logarithms are connected by their star-algebra equivalence.

The ordinary trace pairing gives Pstar as the HS adjoint of P, without dimension normalization. The two partial-trace module laws imply P M_Z(u) Pstar=M_(PZ)(u). With k=inverse(M_(PZ)(u))(PH), set r=H-M_Z(u)Pstar(k). Native continuous-linear inverse cancellation gives Pr=0, and HS self-adjointness gives q(Z,H,u)-q(PZ,PH,u)=q(Z,r,u) for arbitrary complex H. The actual canonical amplification is complex linear on reference blocks: its left and right module laws use linearity, never multiplicativity of a CP map. ConditionalHockeyStickOrthogonalReduction.ptr_amp proves P_out(TX)=P_in(X) for all complex X. Thus the output residual equals T(r) with the same marginal and the same center k. Applying the uniform kernel premise to r gives the conditional arithmetic metric inequality with the unchanged c.

For H=rho-sigma and Z(t)=sigma+tH, positive definite endpoints keep both joint and channel-output segments positive definite. A nonempty traced-out factor gives positive definite PZ(t) by the finite sum of positive principal blocks; trace-one states themselves provide the needed nonemptiness, so empty reference or endpoint carriers introduce no extra state cases. Inverse continuity on the closed u interval proves arithmetic-pairing integrability. Integrating in u and applying arithmetic_inverse_pairing_eq_logDeriv gives the conditional BKM bound. Apply the ordinary UmegakiBKMPath.relativeEntropy_eq_integral_bkm independently to the joint and marginal pairs, cancel the unequal-trace corrections using trace_partialTraceRight, and integrate the pointwise bound with nonnegative weight 1-t. The original weighted BKM integrability justifies subtraction and order; finite reindexing transports the native Fin n theorem, CFC logarithm and actual Bochner derivative. Iterated integration suffices, with no Fubini premise. The similarly named conditional block-family theorem is not used.

This application combines the existing analytic identities with finite-sum and inverse-pairing algebra. The uniform metric premise is an explicit intermediate assumption and is not the entropy conclusion. The application makes no novelty or coefficient-equality claim. Support removal, singular endpoints, the rare-flag ratio construction, the other coefficient directions and final division by a strictly positive finite denominator remain outside this faithful implication. The original all-finite contraction-coefficient chain remains unproved, with open-problem KPI zero.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.affineKernel_integrable`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_apply`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsArithmeticMap_isInvertible`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hsInner_matrix`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.hs_pair_spectral`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiArithmeticBKM.matrixHS`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace](../Lieb/HilbertSchmidtOperatorSpace.md)
