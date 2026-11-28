# Relative entropy under binary pinching

## Abstract

Strict one-eighth relative entropy bounds for faithful binary pinchings and their ordered composition.

Use ordinary traces, faithful density states, and complex matrices. For a Hermitian involution W, write P_W(X) = (X + WXW)/2 and D(ρ∥τ) = Re Tr[ρ(log ρ − log τ)]. The logarithm is the real continuous functional calculus of a Hermitian matrix.

**Definition 1.1 (Finite complex matrices).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.Mat`

*Formalization.* `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Mat n is the full algebra of complex n × n matrices indexed by Fin n.

**Definition 1.2 (Binary pinching).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch`

*Formalization.* `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The operation averages the identity and conjugation by W with weights 1/2.

**Theorem 1.3 (Positive definite conjugates).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.conjugate_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.conjugate_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

A Hermitian W with W² = I is unitary, so WXW is positive definite whenever X is.

**Theorem 1.4 (Trace under involutive conjugation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_W_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_W_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If W² = I, cyclicity of the ordinary trace gives Tr(WXW) = Tr X for every complex X.

**Theorem 1.5 (Conjugation of the logarithm).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.log_W_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.log_W_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian X and a Hermitian involution W, functional calculus gives log(WXW) = W(log X)W.

**Theorem 1.6 (Fixed point of the conjugation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If W² = I, then W P_W(X) W = P_W(X) because conjugation interchanges the two summands.

**Theorem 1.7 (Trace pairing with fixed observables).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_mul_pinch_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_mul_pinch_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Whenever WLW = L, cyclicity gives Re Tr[P_W(X)L] = Re Tr[XL]. The split uses this for the logarithms of the pinched state and the fixed reference.

**Theorem 1.8 (Faithfulness under pinching).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For faithful X and a Hermitian involution W, the average of the two positive definite matrices is positive definite.

**Theorem 1.9 (Matrix formula for relative entropy).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_on_matrices`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_on_matrices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The matrix star algebra equivalence transports the two Hermitian logarithms, giving the ordinary real trace formula for the repository’s relative entropy.

**Definition 1.10 (Pinched density state).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinchState`

*Formalization.* `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinchState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The pinched matrix defines a density state because it is positive definite and its trace equals the original trace one.

**Theorem 1.11 (Exact split against a fixed reference).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If ρ and τ are faithful and WτW = τ, set σ = P_Wρ. Then D(ρ∥τ) = D(ρ∥σ) + D(σ∥τ). Conjugation fixes log σ and log τ. Applying the fixed trace pairing to both logarithms cancels the cross term.

**Theorem 1.12 (Ordered pinching and channel data processing).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For faithful ρ set ρ_U = P_Uρ, ρ_V = P_Vρ, and F = P_Uρ_V. Then D(ρ∥F) = D(ρ∥ρ_U) + D(ρ_U∥F) ≤ D(ρ∥ρ_U) + D(ρ∥ρ_V). The split applies because U fixes F. The channel P_U is an equal mixture of the identity and unitary conjugation by U. Its action sends (ρ, ρ_V) to (ρ_U, F). Canonical channel data processing bounds the extended divergence at these outputs, and faithfulness of the references identifies both extended divergences with their finite trace-log values. The ordered comparison holds for any two Hermitian involutions. When the conjugations commute, F is the common twirl.

For a positive definite complex matrix X and a Hermitian involution W, put Y = WXW, A = P_WX = (X + Y)/2, and K = (X − Y)/2. Write S_W(X) = Re Tr[(X − Y)(log X − W(log X)W)]. The affine segment A + tK is positive definite for −1 ≤ t ≤ 1. All traces are ordinary.

**Theorem 1.13 (One-eighth bound on the matrix trace loss).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_bound_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_bound_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Re Tr[X(log X − log A)] ≤ S_W(X)/8, with strict inequality if A ≠ X. Both sides vanish when A = X. The matrix inequality is homogeneous under positive rescaling.

**Theorem 1.14 (Relative-entropy loss of a faithful state).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a faithful density state ρ, D(ρ∥P_Wρ) ≤ S_W(ρ)/8, strictly when P_Wρ ≠ ρ. The proof uses pinch_bound_matrix and the matrix trace formula for relative entropy.

Let h(t) = Re Tr[(A + tK) log(A + tK)], E(t) = (h(t) + h(−t))/2, and G = E′. The trace-entropy and affine log derivative theorems give G′(t) as the integral over z > 0 of the average of the two resolvent kernels at t and −t. The kernel at t is Re Tr(KR_t K R_t), where R_t = (A + tK + zI)⁻¹. At each shift normalize by the inverse square root of A + zI. The resulting Hermitian congruence C_z = (A + zI)⁻¹ᐟ² K (A + zI)⁻¹ᐟ² has eigenvalues c whose contributions to the averaged kernel are c²(1 + t²c²)/(1 − t²c²)². They increase on [0,1], strictly for each nonzero c. If K ≠ 0, the invertible congruence gives at least one nonzero eigenvalue at every z > 0, so the integrated symmetrized Hessian is strictly increasing.

Thus G is strictly convex when K ≠ 0. Since G(0) = 0, G(t) < tG(1) for 0 < t < 1. Conjugation interchanges the endpoints and the fixed-log trace pairing gives E(1) − E(0) = Re Tr[X(log X − log A)]. Integrating the chord gives the strict upper bound G(1)/2 = S_W(X)/8, using X − Y = 2K and log Y = W(log X)W.

For the limiting sharpness calculation, take X = diag(1 + ε, 1 − ε)/2, with 0 < ε < 1, and let W swap the two coordinates. The pinched state is I/2. The entropy loss is [(1 + ε) log(1 + ε) + (1 − ε) log(1 − ε)]/2 = ε²/2 + O(ε⁴), while S_W(X) = 2ε log((1 + ε)/(1 − ε)) = 4ε² + O(ε⁴). Their ratio tends to 1/8 as ε tends to zero. This scalar limit is the sharpness argument accompanying the formal inequality.

**Theorem 1.15 (One-eighth bound for the ordered loss).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For faithful ρ, D(ρ∥P_U(P_Vρ)) ≤ (S_U(ρ) + S_V(ρ))/8. The inequality is strict if P_Uρ ≠ ρ or P_Vρ ≠ ρ. The exact two-pinching comparison bounds the ordered loss by D(ρ∥P_Uρ) + D(ρ∥P_Vρ). Both single-pinching bounds are evaluated at the original ρ. When either pinching changes ρ, that summand has a strict bound and the other has a weak bound.

In any complex orthonormal spectral frame of ρ with eigenvalues p_i, S_W(ρ)/8 is the sum over ordered pairs (i,k) of |⟨u_i,Wu_k⟩|²(p_i − p_k)(log p_i − log p_k)/8. At ties, equal-eigenvalue terms vanish and the weights between distinct eigenspaces sum to Tr(P_i W P_k W) for their spectral projections. This identifies the entropy weights in the faithful tracial-spectator comparison at cubic exponent in Wu v1, equations (3.54)–(3.55). For the tracial spectator, the lifted Pauli conjugations commute and F = (I/2) ⊗ Tr_s ρ. Equation (13.5) of the theory chapter gives the exact split and the channel comparison. Proposition 17.2 of the Wu theory chapter expresses the split as two sequential losses, with the second pinching applied to ρ_U. Equations (17.3)–(17.5) give the positive-part integral and identify the one-step gaps and the DPI slack D(ρ∥ρ_V) − D(ρ_U∥F).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.Mat`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.conjugate_posDef`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.log_W_conjugate`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinchState`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_bound_matrix`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_fixed`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.pinch_posDef`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_on_matrices`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.relativeEntropy_pinch_split`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_W_conjugate`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.trace_mul_pinch_fixed`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPinchingEntropyResolvent.two_pinching_entropy_comparison`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiBKMPath](../Divergence/UmegakiBKMPath.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup](../ProcessReconstruction/HiddenProcessSemigroup.md)
