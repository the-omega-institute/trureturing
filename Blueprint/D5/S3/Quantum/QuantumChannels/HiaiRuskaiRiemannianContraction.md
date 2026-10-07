# Exact Riemannian contraction coefficients of a qubit CQ channel

## Abstract

The dual WY, geometric and BKM Riemannian contraction coefficients of the non-unital qubit CQ channel equal the three bounds in Hiai and Ruskai's Conjecture 6.3. Each supremum is attained at the maximally mixed input and the Pauli X tangent.

**Definition 1.1 (The operator in a Hermitian eigenbasis).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall h \in \operatorname{Matrix.IsHermitian}\left(rho\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{omegaHermitian}\left(k, rho, h, X\right) = let U := (\operatorname{Matrix.IsHermitian.eigenvectorUnitary}\left(h\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)); let lam := \operatorname{Matrix.IsHermitian.eigenvalues}\left(h\right); let Y := \operatorname{Matrix.conjTranspose}\left(U\right) \cdot X \cdot U; let Z := fun (i : \operatorname{Fin}\left(2\right)) \mapsto fun (j : \operatorname{Fin}\left(2\right)) \mapsto (\frac{k\left(\frac{lam\left(i\right)}{lam\left(j\right)}\right)}{lam\left(j\right)} : \mathbb{C}) \cdot Y\left(i, j\right); U \cdot Z \cdot \operatorname{Matrix.conjTranspose}\left(U\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.omegaHermitian` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Section 2.4, p. 7: "Given a function κ ∈ K we define, for any A ∈ P_d, a linear map Ω_A^κ : M_d → M_d by" the displayed functional-calculus expression in the cited note. In the eigenbasis of rho, a matrix unit with indices i and j has eigenvalue k(lam i / lam j) / lam j. U is the unitary eigenvector matrix; lam is the eigenvalue function. The real coefficient is coerced to C before multiplication.

**Definition 1.2 (The spectral metric operator).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{omega}\left(k, rho, X\right) = if h : \operatorname{Matrix.IsHermitian}\left(rho\right) then \operatorname{omegaHermitian}\left(k, rho, h, X\right) else 0$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.omega` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

The spectral definition agrees with the source's operator on positive definite matrices. Its value at a non-Hermitian foot point is zero; only positive definite foot points occur in the contraction coefficient.

**Definition 1.3 (The qubit CQ channel).**

$$\forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{phi}\left(alpha, tau, X\right) = let wzero := \frac{\operatorname{Matrix.trace}\left(X\right)}{2}; let wone := \frac{\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.FiniteDimensional.qubitX} \cdot X\right)}{2}; \operatorname{SMul.smul}\left(wzero, (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right) + \operatorname{SMul.smul}\left((alpha : \mathbb{C}) \cdot wone, \operatorname{D5.S3.Quantum.FiniteDimensional.qubitX}\right) + \operatorname{SMul.smul}\left((tau : \mathbb{C}) \cdot wzero, \operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.phi` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Section 6, p. 19: "The next theorem treats a family of trace-preserving maps Φ_{α,τ} : M_2 → M_2 with two real parameters α,τ determined by t = (0,0,τ)^t and T = diag(α,0,0); more explicitly," followed by the channel equation quoted in the cited note. The coefficients w0 = trace X / 2 and w1 = trace (qubitX * X) / 2 give the complex linear extension to all matrices. qubitX and qubitZ are the Pauli matrices from FiniteDimensional.

**Definition 1.4 (The real metric quadratic form).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{metric}\left(k, rho, A\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{Matrix.conjTranspose}\left(A\right) \cdot \operatorname{omega}\left(k, rho, A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.metric` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Section 2.4, p. 8: "Associated with κ ∈ K a Riemannian metric M^κ on the Riemannian manifold D_d is defined by" equation (17), quoted in the cited note. The diagonal quadratic form is the Hilbert-Schmidt pairing of A with Omega(A). The displayed trace has zero imaginary part, so its real part is the source's quadratic form.

**Definition 1.5 (An input's contraction ratio).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{ratio}\left(k, alpha, tau, rho, A\right) = \frac{\operatorname{metric}\left(k, \operatorname{phi}\left(alpha, tau, rho\right), \operatorname{phi}\left(alpha, tau, A\right)\right)}{\operatorname{metric}\left(k, rho, A\right)}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.ratio` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

The numerator evaluates the same kernel at the channel image of the state and tangent. The denominator is strictly positive for each of the three kernels, every positive definite input and every nonzero tangent.

**Definition 1.6 (The Riemannian contraction coefficient).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; \operatorname{eta}\left(k, alpha, tau\right) = \operatorname{sSup}\left(\{z : \mathbb{R} \mid \exists rho \in \{rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right) // (\operatorname{Matrix.PosDef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = 1)\},\; \exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; ((\operatorname{Matrix.IsHermitian}\left(A\right)) \land (\operatorname{Matrix.trace}\left(A\right) = 0)) \land ((A \ne 0) \land (z = \operatorname{ratio}\left(k, alpha, tau, \operatorname{Subtype.val}\left(rho\right), A\right)))\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.eta` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Section 2.4, p. 8: "For each κ ∈ K the contraction coefficient of a CPT map Φ with respect to the monotone metric M^κ induced by κ is defined by" equation (19), quoted in the cited note. The supremum runs over rho in the strict density domain and A in the traceless Hermitian space with A nonzero. The subtype value operation exposes the underlying matrix; no input or tangent is restricted to a chosen Pauli direction.

**Definition 1.7 (The dual Wigner-Yanase kernel).**

$$\forall x \in \mathbb{R},\; \operatorname{kDualWY}\left(x\right) = \frac{(1 + \operatorname{Real.sqrt}\left(x\right))^{2}}{4 \cdot x}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.kDualWY` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Theorem 6.2, equation (45c): the dual WY kernel is (1 + sqrt x)^2 / (4 x).

**Definition 1.8 (The non-unital channel parameters).**

$$\forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; (\operatorname{admissible}\left(alpha, tau\right)) \Leftrightarrow ((0 \le alpha) \land ((0 < \left|tau\right|) \land ((\left|tau\right| < 1) \land ((alpha)^{2} + (tau)^{2} \le 1))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.admissible` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

Section 6, p. 19: "Below we assume that α ≥ 0 and α² + τ² ≤ 1." The nonsingular non-unital range is 0 < |tau| < 1. There is no strict positivity condition on alpha.

**Definition 1.9 (Hiai-Ruskai Conjecture 6.3).**

$$(claim) \Leftrightarrow (\forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; (\operatorname{admissible}\left(alpha, tau\right)) \Rightarrow ((\operatorname{eta}\left(\operatorname{kDualWY}, alpha, tau\right) = \frac{(alpha)^{2} \cdot \left(1 + \operatorname{Real.sqrt}\left(1 - (tau)^{2}\right)\right)}{2 \cdot \left(1 - (tau)^{2}\right)}) \land ((\operatorname{eta}\left(fun (x : \mathbb{R}) \mapsto \operatorname{Real.rpow}\left(x, 0 - \frac{1}{2}\right), alpha, tau\right) = \frac{(alpha)^{2}}{\operatorname{Real.sqrt}\left(1 - (tau)^{2}\right)}) \land (\operatorname{eta}\left(\operatorname{dslope}\left(\operatorname{Real.log}, 1\right), alpha, tau\right) = \frac{(alpha)^{2} \cdot \operatorname{Real.log}\left(\frac{1 + tau}{1 - tau}\right)}{2 \cdot tau}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.claim` (`✓ std3`).

*Citation.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

The arXiv v1 PDF, p. 19: "Although the bounds in the above theorem are sufficient to disprove two conjectures as remarked below, we believe that they are optimal, i.e.," "Conjecture 6.3. Equality holds in (45c) through (45e) above." The three equations below encode (45c), (45d), and (45e), respectively. Equation (45d) uses the geometric kernel fun x : ℝ => Real.rpow x (-1/2). Equation (45e) uses dslope Real.log 1, which equals Real.log x / (x - 1) away from x = 1 and has the continuous value 1 at x = 1. The carrier is Matrix (Fin 2) (Fin 2) C; the supremum ranges over every positive definite trace-one input and every nonzero traceless Hermitian tangent. Both signs of tau and alpha = 0 are included.

**Theorem 1.10 (All three bounds are exact).**

$$\forall alpha \in \mathbb{R},\; \forall tau \in \mathbb{R},\; (\operatorname{admissible}\left(alpha, tau\right)) \Rightarrow ((\operatorname{eta}\left(\operatorname{kDualWY}, alpha, tau\right) = \frac{(alpha)^{2} \cdot \left(1 + \operatorname{Real.sqrt}\left(1 - (tau)^{2}\right)\right)}{2 \cdot \left(1 - (tau)^{2}\right)}) \land ((\operatorname{eta}\left(fun (x : \mathbb{R}) \mapsto \operatorname{Real.rpow}\left(x, 0 - \frac{1}{2}\right), alpha, tau\right) = \frac{(alpha)^{2}}{\operatorname{Real.sqrt}\left(1 - (tau)^{2}\right)}) \land (\operatorname{eta}\left(\operatorname{dslope}\left(\operatorname{Real.log}, 1\right), alpha, tau\right) = \frac{(alpha)^{2} \cdot \operatorname{Real.log}\left(\frac{1 + tau}{1 - tau}\right)}{2 \cdot tau})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Mary Beth Ruskai (2016). *Contraction coefficients for noisy quantum channels*. DOI: [10.1063/1.4936215](https://doi.org/10.1063/1.4936215). URL: <https://arxiv.org/abs/1508.03551v1>.

*Commentary.*

For every extreme kernel, a scalar pinching identity bounds the input metric below by 4 y1^2 / (1 - w1^2), and the exact output formula bounds the numerator by the extreme coefficient times that same quantity. Integrating both inequalities with the positive geometric and BKM weights preserves their common denominator. The BKM kernel is dslope Real.log 1. The dual WY kernel is the half mixture of the zero extreme kernel and fun x : ℝ => Real.rpow x (-1/2). The common pair rho = I/2 and A = qubitX attains every upper bound. The argument treats alpha = 0 and both signs of tau.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.admissible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.eta`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.kDualWY`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.metric`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.omega`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.omegaHermitian`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.phi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.ratio`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.result`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
