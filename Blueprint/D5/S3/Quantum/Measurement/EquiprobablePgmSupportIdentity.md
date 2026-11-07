# Actual PGM support, valid bounds and minimality

## Abstract

Actual PGM support, valid bounds and minimality

**Theorem 1.1 (Finite Hermitian variance).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_frob_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_frob_sum` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For any nonempty finite B and any Hermitian matrix family X_i, the sum of squared Frobenius distances to its arithmetic mean is sum_B ||X_i||_F^2-||sum_B X_i||_F^2/|B|. This proof helper is consumed by both the centered actual PGM identity and the actual discrimination bound; it is not a separate physical assumption.

**Theorem 1.2 (Moore-Penrose quarter-power normalization).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.support_quarter_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.support_quarter_normalization` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every finite index type n and every positive semidefinite complex n-by-n matrix Q, put R=Q^(-1/4) using the existing continuous functional calculus. Then R R=Q^(-1/2) and R Q R=sqrt(Q). The scalar negative powers are zero at the zero eigenvalue. Thus these are Moore-Penrose powers and no inverse or full-rank assumption is hidden in the notation.

**Theorem 1.3 (The complete centered score identity).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_identity` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Let N>0, let rho_i be positive semidefinite matrices on C^d with trace one, and let B be any nonempty subset of Fin N, with m=|B|. Put sigma_i=rho_i/N, S_B=sum_(i in B) sigma_i and R_B=S_B^(-1/4). With the existing pgmScore and squared Frobenius norm RHLinalg.frobSq=Re tr(X†X), the exact identity is P_B-1/N=sum_(i in B) ||R_B sigma_i R_B-(1/m)sqrt(S_B)||_F^2. The original weights 1/N are retained; this is not the renormalized m-label score. The proof first sums the sandwiches to sqrt(S_B), expands the finite variance, identifies each actual PGM trace term by cyclicity, and uses tr(S_B)=m/N. It includes m=1 and N=1, zero eigenvalues, repeated eigenvalues, and noncommuting states. A zero-dimensional state space cannot satisfy the trace-one hypotheses for a nonempty B.

**Theorem 1.4 (The nonnegative original-prior advantage).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.random_guessing_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.random_guessing_le` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

Under exactly the density and nonempty-label hypotheses of the centered identity, P_B>=1/N because every squared Hilbert-Schmidt term is nonnegative. In particular singularity does not invalidate the baseline. No comparison between two differently normalized averages follows from this nonnegativity.

**Theorem 1.5 (Shared diagonal support inverse square root).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_inverse_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_inverse_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite real diagonal family s>=0, the actual CFC inverse square root is diagonal(sqrt(s)^(-1)), including zero entries. This helper is consumed by diagonal_score and the symmetric two-coordinate calculation; it is not a separate foundation.

**Theorem 1.6 (The full diagonal support formula).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_score`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_score` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every d,N with N>0, every nonnegative real family p_i(x), and every label set B, the actual old CFC pgmScore of rho_i=diag(p_i) is (1/N) sum_(i in B) sum_x p_i(x)^2/(sum_(j in B) p_j(x)). A zero spectral mass has inverse zero. Empty B and singular support are permitted. Normalization sum_x p_i(x)=1 is not needed for the evaluation; with it these are actual density matrices. This universal diagonal formula is the supplier for the commuting control and dimension-one minimality.

**Theorem 1.7 (Joint support and actual effects).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_support` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every finite-dimensional positive semidefinite ensemble, every finite label subset B (also empty), sigma_i=rho_i/N and S=sum_B sigma_i, the existing spectralSupport(S) is a Hermitian projection. It supports each selected sigma_i on both sides. The actual effects pgmEffects_i=1_(i in B) S^(-1/2) sigma_i S^(-1/2) are positive semidefinite and sum to that projection. The inverse powers are zero on the kernel. No full rank or trace-one condition is used for this support statement.

**Theorem 1.8 (An actual POVM on singular support).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_completion` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every positive semidefinite ensemble on C^(k+1), every B and b in B, add I-P to the b-th support PGM effect. The resulting effects form an actual finitePOVM, vanish outside B, and their actual success equals pgmScore rho B. Positivity of the complement is inherited from the existing star-projection order theorem. Its contribution to the selected score is zero because the states are supported on P.

**Theorem 1.9 (Both valid bounds, with actual active labels).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.actual_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.actual_bounds` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For N>0, arbitrary positive semidefinite trace-one rho_i, and every actual finitePOVM E on C^(k+1), let A be its nonzero-effect labels and m=|A|. Then A is nonempty and success(rho,E)<=min(1/N+sqrt((m-1)(P_A-1/N)/N),1/N+sqrt((N-1)(P_all-1/N)/N)). In particular this holds for every optimal POVM, without an existence premise or an ordering between the two bounds. Singular averages, m=1 and N=1 are included. The proof uses the actual quarter-power sandwiches, support containment, centered Frobenius variance, PSD cross terms and finite matrix Cauchy-Schwarz. These are two independent valid estimates; the disproved comparison is not a premise.

**Theorem 1.10 (The singleton support endpoint).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.singleton_score`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.singleton_score` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every positive N, every PSD trace-one family rho_i on C^d, and every label i, the actual original-prior singleton CFC score is P_{i}=1/N. Singular states are allowed. This follows from the support quarter-power sandwich in the centered identity and includes N=1.

**Theorem 1.11 (Every one-dimensional score).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.dimension_one_score`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.dimension_one_score` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every N>0, every trace-one one-dimensional matrix family and every nonempty B, P_B=1/N. In dimension one trace normalization fixes every matrix to I; the universal diagonal CFC formula gives the result. Thus the comparison is equality in dimension one.

**Theorem 1.12 (No violation with at most two labels).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.at_most_two_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.at_most_two_labels` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every 0<N<=2, every PSD trace-one ensemble in any finite dimension and every nonempty B, (|B|-1)(P_B-1/N)<=(N-1)(P_all-1/N). This is stronger than restricting B to an optimum’s active set. A singleton has zero centered score by singleton_score; otherwise B is all labels and the comparison is equality. Together with the reused actual three-state qubit rational refutation, this proves minimality d=2,N=3 for violation.

**Theorem 1.13 (The limited pure-pair geometric control).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_pair_population`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_pair_population` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For real 0<z<1 and a pure Bloch vector (x,y,w) with x^2+y^2+w^2=1, membership in the ball x^2+y^2+(w-z)^2<=1-z^2 implies w>=z and (1-w)/2<=(1-z)/2, with the latter reference population positive. The symmetric pure pair has Bloch vectors (+/-sqrt(1-z^2),0,z). This is a limited mechanism restriction, not a general all-pure comparison theorem. The general all-pure and quantitative spectral-floor questions remain open in the supplied sources.

**Theorem 1.14 (Actual active-ensemble reduction).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.active_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.active_reduction` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For arbitrary N>0, m>0 and actual density matrices, if E is an actual optimal finitePOVM and e enumerates exactly its nonzero effects by Fin m, then the same active states and effects form a normalized actual m-label density/POVM optimum. The original success equals (m/N) times that normalized optimum; every reduced competing POVM is extended by zero effects to prove the optimization transfer. No full-rank condition is used, and m=1 and N=1 remain in scope.

**Theorem 1.15 (Limited control for an actual pure omitted state).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_density_control`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_density_control` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For 0<z<1, every actual PSD trace-one idempotent qubit state rho whose pure symmetric-pair dual slack [(1+sqrt(1-z^2))I+zZ]/6-rho/3 is PSD satisfies Re rho_11<=(1-z)/2. The proof reconstructs its actual Bloch vector with the existing ActualPureQubitGeometry owner, obtains norm one and the dual ball, and consumes pure_pair_population. This is the limited mechanism control; the general all-pure PGM comparison remains open.

Source custody: the mechanism manuscript is anonymous (3 November 2026); no license grant was supplied. The old literal byline remains Wenlin Zhang and Haobo / trureturing, and its actual rational proof is reused as EquiprobablePgmActiveSetRefutation.result. The new note is by Haobo Ma then Wenlin Zhang (4 November 2026), with CC BY 4.0 restricted to that new note. Hyunho Cha is credited for the symmetric scores and qubit/commuting constructions. The metadata URLs locate immutable repository citation records, not public manuscript originals. Activity means a nonzero effect, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open. No priority or publication claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.active_reduction`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.actual_bounds`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.at_most_two_labels`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_frob_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.centered_identity`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_inverse_sqrt`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.diagonal_score`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.dimension_one_score`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_completion`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pgm_support`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_density_control`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.pure_pair_population`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.random_guessing_le`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.singleton_score`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.support_quarter_normalization`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransport](../Lieb/SupportPerspectiveTransport.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation](EquiprobablePgmActiveSetRefutation.md)
