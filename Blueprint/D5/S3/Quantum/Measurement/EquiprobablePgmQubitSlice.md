# EquiprobablePgmQubitSlice

## Abstract

Universal actual-object PGM control

**Theorem 1.1 (The complete positive qubit interval).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.family` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For every 0<t<=1/55, the actual states [[1-t^2,+/-t/2],[+/-t/2,t^2]] and diag(1-10t^2,10t^2) are strictly positive trace-one mixed qubits. The actual unique optimal finitePOVM is (Q+,Q-,0), with success (1+t)/3. Actual centered CFC scores are eta_A=t/(6sqrt(1-t^2)) and eta=t/(18sqrt(1-4t^2))+3t^2/[2(1-4t^2)]. The actual gap eta_A-2eta is at least t(1-54t-12t^2)/[18(1-4t^2)]>0, including the endpoint; 1-54/55-12/55^2=43/3025. The cutoff is sufficient and is not optimized.

**Theorem 1.2 (Exact cubic-order asymptotic statements).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.asymptotics`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.asymptotics` (`✓ std3`). ∎

*Citation.* Anonymous (2026). *Why the Active-Set PGM Comparison Can Fail: Mechanism, a minimal qubit family, and a classical model*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/anonymous2026pgmmechanism.md>.

*Commentary.*

For the actual scores as t tends to zero through positive parameters, eta_A=t/6+O(t^3), eta=t/18+3t^2/2+O(t^3), and eta_A-2eta=t/18-3t^2+O(t^3), in the precise filter-based IsBigO sense. The centered ratio eta_A/eta tends to three and raw ratio P_A/P tends to one. The proof rationalizes the square-root residuals and bounds the continuous cubic coefficients, using eventual equalities to the actual scores. t=0 is not a physical member asserted by this result.

The construction and symmetric calculations are credited to Hyunho Cha. Mechanism attribution remains anonymous; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. CC BY 4.0 applies to the new note only. The original nonzero-effect interpretation of activity is retained, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.asymptotics`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmQubitSlice.family`
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmLoading](EquiprobablePgmLoading.md)
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity](EquiprobablePgmSupportIdentity.md)
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)
