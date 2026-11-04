# Error and disturbance below the endpoint minimum

## Abstract

A rational three-dimensional measurement has overall error below both endpoint quantities.

**Theorem 1.1 (Unitary basis projectors resolve the identity).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\sum_{\left(i: \operatorname{Fin}\left(d\right)\right)} \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(a, i\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.sum_projectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-one projectors onto the columns of any unitary matrix sum to the identity.

**Definition 1.2 (State-dependent labeled error).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.errorAt}\left(\rho, a, c\right): \mathbb{R}\right) = \operatorname{iSup}\left(\lambda \left(i: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\left|\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\rho \cdot \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(a, i\right) - \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(c, i\right)\right)\right)\right)\right|\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.errorAt` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

For a complex matrix ρ, take the supremum over the labeled outcomes i of the absolute real part of the trace against the difference of the two rank-one projectors. For a density matrix this is the infinity distance between the two outcome distributions. The bases a and c are the columns of unitary matrices. This is the error of new_912arxiv.tex, lines 182–197. The definition itself is given for every matrix ρ and every natural dimension d.

**Definition 1.3 (State-dependent disturbance).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.disturbanceAt}\left(\rho, c, b\right): \mathbb{R}\right) = \operatorname{iSup}\left(\lambda \left(j: \operatorname{Fin}\left(d\right)\right) \mapsto \left(\left|\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\rho \cdot \left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(b, j\right) - \operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(c\right), \operatorname{D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation.measurementProjector}\left(b, j\right)\right)\right)\right)\right)\right|\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.disturbanceAt` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

For outcome j of b, subtract from its projector its image under the unread projective measurement in c, and take the absolute real part of its expectation in ρ. The supremum over j is the infinity distance between the b distributions before and after that measurement when ρ is a density matrix. Here unreadState sends an observable X to the sum of QₖXQₖ over the projectors Qₖ of c. This expresses new_912arxiv.tex, lines 175–197, in terms of observables.

**Definition 1.4 (Overall error in one common state).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.overallError}\left(a, c, b\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(t: \mathbb{R}\right) \mid \exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \land \left(t = \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.errorAt}\left(\rho, a, c\right) + \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.disturbanceAt}\left(\rho, c, b\right)\right)\right)\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.overallError` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

Take the real supremum of the sum of labeled error and disturbance over density matrices ρ. Both summands use the same ρ; the expression is not the sum of two separately optimized quantities. This is the overall error defined in new_912arxiv.tex, lines 215–223.

**Definition 1.5 (State-independent labeled error).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.error}\left(a, c\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(t: \mathbb{R}\right) \mid \exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \land \left(t = \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.errorAt}\left(\rho, a, c\right)\right)\right)\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.error` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

The state-independent labeled error is the supremum of errorAt over positive semidefinite complex matrices of trace one. The labels of the columns of a and c are kept fixed. This is the state-independent error of new_912arxiv.tex, lines 200–204, with the maximum written as a real supremum.

**Definition 1.6 (State-independent disturbance).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.disturbance}\left(c, b\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(t: \mathbb{R}\right) \mid \exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \land \left(t = \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.disturbanceAt}\left(\rho, c, b\right)\right)\right)\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.disturbance` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

The state-independent disturbance is the supremum of disturbanceAt over positive semidefinite complex matrices of trace one. This is new_912arxiv.tex, lines 200–209, with the maximum written as a real supremum. No lower bound on d is imposed in these definitions.

**Definition 1.7 (Permuting the outcome labels).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(\pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(d\right)\right)\right), \left(\left(\operatorname{Subtype.val}\left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.relabel}\left(b, \pi\right): \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{Matrix.submatrix}\left(\operatorname{Subtype.val}\left(b\right), \operatorname{Equiv.toFun}\left(\operatorname{Equiv.refl}\left(\operatorname{Fin}\left(d\right)\right)\right), \operatorname{Equiv.toFun}\left(\pi\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

The permutation π reorders the columns of b while the row indices are fixed. Thus column i of the relabeled basis is column π(i) of b. Reindexing rows and columns by equivalences preserves unitarity, so the resulting matrix again defines an element of the unitary group. Subtype.val specifies the underlying matrix; its unitarity proof does not affect the value.

**Definition 1.8 (Error with freely relabeled outcomes).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.relaxedError}\left(a, b\right): \mathbb{R}\right) = \operatorname{iInf}\left(\lambda \left(\pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(d\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.error}\left(a, \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.relabel}\left(b, \pi\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.relaxedError` (`✓ std3`).

*Citation.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

Take the infimum of the labeled error over every permutation π of Fin d. Since this permutation type is finite and nonempty, it is a minimum. It implements the disregard of outcome labels in new_912arxiv.tex, lines 614–620.

**Definition 1.9 (The proposed lower bound on overall error).**

$$\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.claim}: \operatorname{Prop}\right) = \left(\forall \left(d: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le d\right) \to \left(\forall \left(a: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(c: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(b: \operatorname{CoeSort.coe}\left(\operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\operatorname{min}\left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.relaxedError}\left(a, b\right), \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.disturbance}\left(a, b\right)\right) \le \operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.overallError}\left(a, c, b\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

For every natural d at least two and every three unitary measurement bases a, c and b, the proposed inequality bounds overallError from below by the minimum of the relaxed error between a and b and the disturbance of b caused by a. This is the second inequality of Conjecture 3 in new_912arxiv.tex, lines 623–639, with only the endpoint error relaxed over outcome labels. It asserts neither the first inequality nor the equality conditions.

**Theorem 1.10 (A rational counterexample in dimension three).**

$$\neg \left(\operatorname{D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-wu-chau-2016-error-disturbance-endpoint-refutation` (refuted) by `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-wu-chau-2016-error-disturbance-endpoint-refutation","declaration_gid":"D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S.S. Zhou; Shengjun Wu; H.F. Chau (2016). *State-independent error-disturbance trade-off for measurement operators*. DOI: [10.1016/j.physleta.2016.03.046](https://doi.org/10.1016/j.physleta.2016.03.046). URL: <https://arxiv.org/abs/1509.03812v1>.

*Commentary.*

Take a to be the standard basis in dimension three. Let C be the unitary whose rows are (312/313, −25/313, 0), (25/313, 312/313, 0), (0, 0, 1). Let B have rows (32976/33205, −3757/33205, −1020/33205), (3893/33205, 31824/33205, 8640/33205), (0, −8700/33205, 32045/33205). Their products with their conjugate transposes are the identity, by exact rational arithmetic. Write Pᵢ, Qᵢ and Rⱼ for the rank-one projectors of a, C and B, respectively. Set Eᵢ = Pᵢ − Qᵢ and Dⱼ = Rⱼ − ∑ₖ QₖRⱼQₖ.

Each projector entry is the product of a column entry and the conjugate of another entry in the same column. Expanding these products gives exact rational tables for Eᵢ and Dⱼ. In particular E₁ = −E₀ and E₂ = 0, with indices starting at zero. Put s = 71/250. For each j in Fin 3 and each of the four sign pairs ε, δ in {1, −1}, the matrix sI − (εE₀ + δDⱼ) has an exact factorization L diag(q) Lᴴ with all three entries of q nonnegative. The diagonal matrix is positive semidefinite, and conjugation by L preserves that property. These twelve factorizations therefore establish positivity. The identity E₁ = −E₀ supplies the same bounds at i = 1 by reversing ε. At i = 2, average the two inequalities for ε = 1 and ε = −1 to cancel E₀.

For any density matrix ρ, positivity of sI − (εEᵢ + δDⱼ) implies ε Re tr(ρEᵢ) + δ Re tr(ρDⱼ) ≤ s, using positivity of trace products and tr ρ = 1. The finite outcome suprema are attained. Choose maximizing indices i and j and choose each sign according to the sign of its real expectation. Their sum of absolute values is at most s, so errorAt ρ a C + disturbanceAt ρ C B ≤ s for every density matrix. For a nonzero vector x with squared norm n, xxᴴ/n is positive semidefinite and has trace one, by normalization of its trace. Density matrices in dimension three are nonempty; taking the supremum gives overallError a C B ≤ 71/250.

To justify the endpoint suprema, note that the projectors of any unitary basis sum to I. Their complements are sums of the remaining positive semidefinite projectors. For any two effects X and Y with X, Y, I − X and I − Y positive semidefinite, both real expectations in a density matrix lie in [0, 1]; hence |Re tr(ρ(X − Y))| ≤ 1. Measurement in the standard basis sends Rⱼ to its diagonal matrix of diagonal entries. That matrix and its complement are positive semidefinite, by the corresponding diagonal inequalities for Rⱼ and I − Rⱼ. Consequently the sets defining disturbance a B and every error a (relabel B π) are bounded above by 1.

Put r = 57/200. For x = (−5, 11, −10), its squared norm is 246 and the pure state xxᴴ/246 is a density matrix. At outcome j = 1, the expectation of R₁ minus its diagonal part is exactly 2577721016/9041090605, which exceeds r. Its absolute value is therefore a lower bound on disturbanceAt in this state.

For an arbitrary permutation π, split according to π(1). If π(1) = 0 or π(1) = 2, use x = (0, 1, 0), of squared norm 1. If π(1) = 1, use x = (−5, −16, −11), of squared norm 402. In each case xxᴴ divided by that squared norm is a density matrix. The real expectation differences at i = 1 are 20736/21025, 42157045933/147744651350 and 41116897/44102881 when π(1) is 0, 1 and 2, respectively. All three exceed r, so the labeled error exceeds r.

The preceding states and boundedness place disturbance a B and every error a (relabel B π) strictly above r. There are finitely many permutations, so their infimum, relaxedError a B, also exceeds r. Thus the minimum of the two endpoint quantities is strictly greater than 57/200, whereas overallError a C B ≤ 71/250 < 57/200. Applying the proposed inequality at d = 3 to a, C and B gives a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.disturbance`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.disturbanceAt`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.error`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.errorAt`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.overallError`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.relabel`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.relaxedError`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.sum_projectors`
- Dependency: [D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment](../Contextuality/TemporalHardySpinAttainment.md)
- Dependency: [D5/S3/Quantum/CotfasDVGS](../CotfasDVGS.md)
- Dependency: [D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation](../Decoherence/DephasingTwoClassicalityBlockRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
