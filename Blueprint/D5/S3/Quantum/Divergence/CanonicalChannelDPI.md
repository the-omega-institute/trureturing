# Canonical Quantum Channel Data Processing

## Abstract

Support-aware quantum relative entropy decreases under every finite quantum channel.

**Theorem 1.1 (Norm-saturated diagonal logarithm comparison).**

Lean statement: `D5/S3/Quantum/Divergence/CanonicalChannelDPI.diagonal_log_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CanonicalChannelDPI.diagonal_log_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original DPI proof's diagonal logarithm comparison is extracted once with the full positive-spectrum, contraction, matrix comparison, vector mapping and unit norm hypotheses. The original public DPI consumes it. This proof organization claims no independent mathematical gain.

**Theorem 1.2 (Data processing including singular noncommuting states).**

$$\forall u, v: \operatorname{Level},\ a: \operatorname{Type} u, b: \operatorname{Type} v,\ [\operatorname{Fintype}(a)], [\operatorname{DecidableEq}(a)], [\operatorname{Nonempty}(a)],\ [\operatorname{Fintype}(b)], [\operatorname{DecidableEq}(b)], [\operatorname{Nonempty}(b)],\ \phi: \operatorname{QuantumChannel}(a, b),\ \rho, \sigma: \operatorname{DensityState}(a),\ \operatorname{extendedQuantumRelativeEntropy}(\operatorname{mapState}(\phi, \rho), \operatorname{mapState}(\phi, \sigma)) \le \operatorname{extendedQuantumRelativeEntropy}(\rho, \sigma).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The input and output carriers are arbitrary finite decidable nonempty types in independent universes. DensityState is the actual positive semidefinite complex matrix of trace one. QuantumChannel is a bundled completely positive complex-linear trace-preserving map, and mapState is its action on that same state.

The entropy takes values in the real numbers with top adjoined. It equals Re Tr(rho (log rho - log sigma)) when ker(sigma) is contained in ker(rho), and top otherwise. The spectral logarithm uses natural logarithms and is totalized at zero. Singular states and noncommuting pairs remain in the theorem's scope.

One Kraus family gives support transfer and both Schwarz inequalities. The positive-support eigenfamilies give exact trace-log coordinates and a contraction V satisfying V eta = xi, V* V <= I, and V* A V <= B. The square-root defect extends V to an isometry and annihilates eta.

Reflection across the isometry range and finite eigenvector intertwining give logarithm compression. Operator logarithm monotonicity applies to strictly positive regularized matrices. A finite scalar logarithm limit then proves the supported inequality; the unsupported input has top on the right. This is the finite matrix form of the established Petz and Hiai-Mosonyi-Petz-Beny support contraction argument.

Supported quantum Pinsker application. Let n be any finite type with decidable equality, and let rho and sigma be DensityState n. The only state-pair assumption is SupportContained rho sigma, meaning ker(sigma) is contained in ker(rho). No Nonempty n premise is added: if n were empty, the trace of rho would be zero, contradicting its trace-one field. Put mat(tau) = CStarMatrix.ofMatrix.symm tau.1, R = mat(rho), S = mat(sigma), and A = R - S. Thus A is Hermitian and Tr(A) = 0. Write N = traceNorm(A) for the unhalved trace norm, d = N/2 = traceDistance(rho,sigma), and D(rho||sigma) = finiteTraceLogRelativeEntropy rho sigma = Re Tr(rho (log rho - log sigma)). All logarithms below are natural logarithms.

Construct the measurement from A itself. For hA : A.IsHermitian, take U = hA.eigenvectorUnitary.val and lambda_i = hA.eigenvalues i, so A = U diag(lambda_i) U* and U*U = UU* = I. Here * denotes conjugate transpose. Set s(i) = decide(0 < lambda_i), E = diag(1 if s(i) is true, 0 otherwise), and P = U E U*. Consequently P* = P, P^2 = P, and P = cfc (x maps to 1 if 0 < x, 0 otherwise) A. This use of the sign indicator is valid on the finite spectrum, including zero eigenvalues. Since 1_(lambda_i > 0) lambda_i = max(lambda_i,0), the same spectral calculation gives P A = posPart A.

Use the actual binary Kraus family K_i : Matrix Bool n Complex defined entrywise by K_i(b,j) = conjugate(U(j,i)) when b = s(i), and zero otherwise. For each i, (K_i* K_i)(j,k) = U(j,i) conjugate(U(k,i)); hence sum_i K_i* K_i = UU* = I. Applying FiniteKrausChannel.finite_kraus_quantum_channel to this family and this Gram identity supplies one QuantumChannel Phi : QuantumChannel n Bool whose matrix action is Phi(X) := CStarMatrix.ofMatrix.symm (Phi.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = sum_i K_i X K_i*. Complete positivity is the finite Kraus Gram realization: each amplified positive input X = B B* is sent to a sum of products ((I tensor K_i) B) ((I tensor K_i) B)*. Cyclicity of trace and sum_i K_i* K_i = I give Tr(Phi(X)) = Tr(X). Neither the channel nor trace preservation is postulated.

The same family determines both output states. For every matrix X, K_i X K_i* is diagonal with b-entry 1_(b = s(i)) (U* X U)(i,i). Summing gives Phi(X) = diag_b(sum_(i : s(i) = b) (U* X U)(i,i)). Cyclicity of trace identifies the true entry with Tr(P X). Define p = Re Tr(P R) and q = Re Tr(P S). Positivity of each output diagonal and its trace one show 0 <= p,q <= 1, and the actual outputs are mat(Phi.mapState rho) = diag_b(if b then p else 1-p) and mat(Phi.mapState sigma) = diag_b(if b then q else 1-q), with real entries embedded in Complex.

The measurement gap is exactly the original trace distance. CFC.posPart_sub_negPart gives A = posPart A - negPart A, and Tr(A) = 0 makes their real traces equal. FiniteTraceDistance.trace_norm_jordan_mass gives N = Re Tr(posPart A) + Re Tr(negPart A) = 2 Re Tr(posPart A). Therefore p-q = Re Tr(P(R-S)) = Re Tr(P A) = Re Tr(posPart A) = N/2 >= 0. The classical total variation of these very two output distributions is (|p-q| + |(1-p)-(1-q)|)/2 = |p-q| = N/2. There is no assumed maximizing effect or trace-distance premise.

Support transfer retains the singular endpoints. Apply CanonicalChannelDPI.supported_relative_modular_model Phi rho sigma to the input support inclusion; its outputSupport field gives SupportContained (Phi.mapState rho) (Phi.mapState sigma). At q = 0, the true coordinate vector lies in the kernel of the second diagonal output and therefore in the kernel of the first, so p = 0. At 1-q = 0, the false coordinate vector gives 1-p = 0. No strict positivity of either input state, p, q, 1-p, or 1-q is required.

Compute entropy on those same outputs. Transport the matrix functional calculus through CStarMatrix.ofMatrixStarAlgEquiv using StarAlgHomClass.map_cfc; finite_real_spectrum supplies continuity on the finite spectrum. EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal then gives the diagonal logarithms log p, log(1-p) and log q, log(1-q). Expanding the trace yields D(Phi(rho)||Phi(sigma)) = p(log p - log q) + (1-p)(log(1-p) - log(1-q)). For x,y in the two corresponding output coordinates, y = 0 implies x = 0. If x = 0 its entire summand is zero; otherwise y is nonzero and Real.log_div gives x(log x - log y) = x log(x/y). Thus this entropy is literally the Bernoulli KL value k = p log(p/q) + (1-p) log((1-p)/(1-q)). The totalized Real.log at zero, and multiplication by zero, preserve the zero and one endpoints; this calculation never uses a logarithm quotient identity without its nonzero hypotheses.

Apply extended_quantum_relative_entropy_channel_dpi to the constructed Phi and the original ordered pair rho,sigma. SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_coe_of_support rewrites both sides using the input support inclusion and outputSupport, so k <= D(rho||sigma). Apply D5.S3.TotalVariation.Pinsker.binary_pinsker to p,q with their closed-interval bounds and the two endpoint implications just proved; it gives 2 * (p-q)^2 <= k. Substituting p-q = N/2 into this same-measurement inequality gives N^2 / 2 <= k <= D(rho||sigma), hence traceNorm(mat(rho)-mat(sigma))^2 <= 2 * finiteTraceLogRelativeEntropy rho sigma. Equivalently, 2 * traceDistance(rho,sigma)^2 <= D(rho||sigma). The conclusion is an application of the existing finite channel DPI, Jordan mass identity, and classical binary Pinsker inequality.

Supplier pin and scope. The cited project declarations are at repository revision 315311d492533fd23b7199f681561a390d94f0ef: under D5.S3.Quantum, Foundation.FiniteKrausChannel.finite_kraus_quantum_channel, Foundation.FiniteTraceDistance.trace_norm_jordan_mass and traceNorm_nonneg, Divergence.CanonicalChannelDPI.supported_relative_modular_model (defined in CanonicalRelativeModularModel.lean), Divergence.SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_coe_of_support, Divergence.CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi, and Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal; the scalar supplier is D5.S3.TotalVariation.Pinsker.binary_pinsker at the same revision. The spectral and functional-calculus suppliers are from the pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. This finite-dimensional application adds no mathematical declaration and claims neither a new inequality nor library growth. It asserts no physical measurement implementation or computational resource bound.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalChannelDPI.diagonal_log_comparison`
- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
