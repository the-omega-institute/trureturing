# Whole smooth recovery

## Abstract

The original ST37 statement for actual smooth reversible channels and their range bundles.

**Theorem 1.1 (The whole original ST37 theorem).**

Lean statement: `D5/S3/Quantum/Recovery/WholeSmoothRecovery.whole_original_ST37`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/WholeSmoothRecovery.whole_original_ST37` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Let B be an arbitrary compact real smooth manifold, with its original model with corners. Let d, n and k be arbitrary natural numbers with only d > 0 assumed. A smooth family N_x of complex linear matrix channels is completely positive and trace preserving, has a pointwise completely positive trace-preserving left inverse, and satisfies rank(N_x(identity)) = k d. The left inverse is not assumed to vary smoothly. Empty bases, n = 0 and k = 0 retain their original logical scope.

Put Q_x = N_x(identity), P_x = spectralSupport(Q_x), W_x = spectralInverseSqrt(Q_x), and pi_x(T) = W_x N_x(T) W_x. These are the actual spectral functions, with inverse square root zero on the kernel. The theorem proves smoothness of Q, P and W and joint smoothness of pi. It also establishes pi(identity) = P, preservation of adjoints and multiplication, commutation with Q, and N_x(T) = Q_x pi_x(T) for every complex matrix T.

Fix v = 0 in Fin d and set F_x(i,j) = pi_x(e_ij). The explicit decoder uses the matrix-unit Kraus family together with reset Kraus operators single(v,b,1)(identity - P_x). Every Kraus coefficient varies smoothly and the decoder is jointly smooth in x and its matrix input. It is completely positive and trace preserving, recovers every complex T exactly, and recovers after tensoring with the identity at every natural reference dimension. The two coordinate formulas identify it with the matrix-unit trace expression and the corresponding spectral transpose expression.

The support bundle E_x = range(P_x) has complex rank k d. The syndrome bundle F_x = range(F_x(v,v)) has complex rank k. The theorem constructs real smooth prebundles for E, F and the actual canonical complex tensor fibers F_x tensor C^d. It supplies their complex vector-bundle structures, identifies the E and F total-space topologies with their ambient induced topologies, proves the ambient embeddings and their smoothness, and verifies the tensor-chart base sets and action on pure tensors.

A family Theta_x: F_x tensor C^d -> E_x of complex linear isometric equivalences is characterized by Theta_x(w tensor e_i) = F_x(i,v)w. Its inverse has the finite coordinate formula sum_i back_x(y)_i tensor e_i, with back_x(y)_i = F_x(v,i)y in the ambient physical space. The adjoint of Theta is its inverse. The adjoint-composition identities for the two bundle inclusions give the identity on each fiber and the actual ambient projections P_x and F_x(v,v). Both Theta and its inverse are smooth maps of the actual total spaces.

The syndrome endomorphism sigma_x is the restriction of Q_x; sigmaInv_x is the restriction of W_x W_x. Both give smooth total-space maps. The former is positive and has strictly positive real inner product on every nonzero fiber vector, both inverse identities hold, and its complex linear trace is one. The intertwining identity Q_x Theta_x = Theta_x(sigma_x tensor identity) and the channel factorization N_x(T) = U_x(sigma_x tensor T)U_x* hold for all complex T, where U_x is the support inclusion composed with Theta_x.

For the original input-first Choi convention J_x, the theorem proves positivity, rank k, the precise index-swap relation to MatrixMap.choi_matrix, and smoothness of J_x and its actual CFC square root. Reshaping the square-root columns gives the specified redundant Kraus family A_x(mu), with smooth coefficients, exact channel expansion and sum_mu A_x(mu)* A_x(mu) = identity.

The final witness is the actual Stinespring isometry into C^n tensor C^(d n): V_x(u) = sum_mu A_x(mu)u tensor e_mu. The complex Euclidean and tensor norms and inner products are the original ones. Orthogonality of the environment basis and the Kraus normalization prove isometry; the finite tensor sum varies jointly smoothly in x and u. The final coordinate identity reconstructs N_x(T) from the coefficients of this V for every complex T.

The proof reuses the existing pointwise reversible-channel construction and its explicit inverse formula. Actual constant-rank spectral smoothness comes from the Hermitian square-map local inverse and local Gram coordinates. Tensor coefficients in local range-bundle charts prove the global smoothness assertions; no global vector frame, smoothly selected recovery family or extra spectral regularity premise is supplied. The result does not assert ST38, later control statements, or an unresolved external conjecture.

Nayak and Sen establish the finite reversible-channel fixed-ancilla normal form; Choi, Johnston and Kribs supply relevant multiplicative-domain context. The application here specifies actual spectral functions, their smooth parameter dependence, the concrete range and tensor bundles, and the original decoder and redundant Choi-column witnesses. These references do not assert a verbatim external Lean implementation or a new literature priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/WholeSmoothRecovery.whole_original_ST37`
- Dependency: [D5/S3/Geometry/ProjectionRange/ActualRangeTensor](../../Geometry/ProjectionRange/ActualRangeTensor.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](ActualChannelAlgebra.md)
- Dependency: [D5/S3/Quantum/Recovery/MatrixUnitDecoder](MatrixUnitDecoder.md)
- Dependency: [D5/S3/Quantum/Recovery/PointwiseTensorRecovery](PointwiseTensorRecovery.md)
- Dependency: [D5/S3/SpectralTopology/ActualSpectralWhitening](../../SpectralTopology/ActualSpectralWhitening.md)
