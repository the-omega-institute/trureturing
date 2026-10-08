# Finite-Fock beam-splitter non-extremality

## Abstract

Finite-Fock beam-splitter states need not be extreme Wigner-positive states.

Fock cutoff K is represented by Matrix (Fin (K+1)) (Fin (K+1)) Complex. Real coefficients are explicitly mapped by Complex.ofReal; natural coefficients use Nat.cast into Real. The complex order is Mathlib ComplexOrder: a complex value is non-negative precisely when its imaginary part is zero and its real part is non-negative. Nat.sub denotes truncated natural subtraction. Finite indices are sent to their natural values by val. Scalar multiplication uses the Lean scalar action. Proof arguments to beamSplitter are omitted; its transmissivity is one half.

**Definition 1.1 (genLaguerre).**

$$\forall k : \mathbb{N}, (\forall m : \mathbb{N}, (\forall x : \mathbb{R}, (\operatorname{genLaguerre}\left(k, m, x\right) = \sum_{i:\mathbb{N},i \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)}(\frac{(((-(1))^{i}) \cdot (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{choose}\left(m + k, \operatorname{Nat}.\operatorname{sub}\left(m, i\right)\right)\right))) \cdot ((x)^{i})}{\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(i\right)\right)}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.genLaguerre` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

The generalized Laguerre polynomial uses the explicit finite sum with real argument x and natural indices k and m.

**Definition 1.2 (wignerFock).**

$$\forall m : \mathbb{N}, (\forall n : \mathbb{N}, (\forall alpha : \mathbb{C}, (\operatorname{wignerFock}\left(m, n, alpha\right) = \operatorname{ite}\left(m \le n, (((\operatorname{Complex}.\operatorname{ofReal}\left(((\frac{2}{\operatorname{Real}.\operatorname{pi}}) \cdot ((-(1))^{m})) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\frac{\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right)\right)}\right))\right)) \cdot (((2) \cdot (alpha))^{\operatorname{Nat}.\operatorname{sub}\left(n, m\right)})) \cdot (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{genLaguerre}\left(\operatorname{Nat}.\operatorname{sub}\left(n, m\right), m, (4) \cdot ((\left\lVert alpha \right\rVert)^{2})\right)\right))) \cdot (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{exp}\left((-(2)) \cdot ((\left\lVert alpha \right\rVert)^{2})\right)\right)), \operatorname{starRingEnd}\left(\mathbb{C}, (((\operatorname{Complex}.\operatorname{ofReal}\left(((\frac{2}{\operatorname{Real}.\operatorname{pi}}) \cdot ((-(1))^{n})) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\frac{\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{factorial}\left(m\right)\right)}\right))\right)) \cdot (((2) \cdot (alpha))^{\operatorname{Nat}.\operatorname{sub}\left(m, n\right)})) \cdot (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{genLaguerre}\left(\operatorname{Nat}.\operatorname{sub}\left(m, n\right), n, (4) \cdot ((\left\lVert alpha \right\rVert)^{2})\right)\right))) \cdot (\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{exp}\left((-(2)) \cdot ((\left\lVert alpha \right\rVert)^{2})\right)\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.wignerFock` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Appendix A.1, page 18, equation (48), gives the Fock transition Wigner function. Its continuation is stated verbatim: “for m≤n, otherwise use the relation W|n⟩⟨m|=W*|m⟩⟨n|.” The displayed formula includes the real prefactor, complex power, Laguerre polynomial and Gaussian envelope; the reverse branch is complex conjugation.

**Definition 1.3 (wigner).**

$$\forall K : \mathbb{N}, (\forall A : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), (\forall alpha : \mathbb{C}, (\operatorname{wigner}\left(A, alpha\right) = \sum_{m:\operatorname{Fin}\left(K + 1\right)}(\sum_{n:\operatorname{Fin}\left(K + 1\right)}((A\left(m, n\right)) \cdot (\operatorname{wignerFock}\left(\operatorname{val}\left(m\right), \operatorname{val}\left(n\right), alpha\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.wigner` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Page 6, Section 3.1, equation (16): “Consider a quasi-state Â∈𝒜ⁿ, with Fock matrix elements Aₖℓ=⟨k|Â|ℓ⟩. The Wigner function of Â is here expressed as:” The displayed expansion retains every matrix entry, including off-diagonal entries, and includes both endpoints of the Fock cutoff.

**Definition 1.4 (WPS).**

$$\forall K : \mathbb{N}, (\operatorname{WPS}\left(K\right) = \{A:\operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right)\mid \operatorname{Matrix}.\operatorname{PosSemidef}\left(A\right) \land \left(\operatorname{Matrix}.\operatorname{trace}\left(A\right) = 1 \land \forall alpha : \mathbb{C}, (0 \le \operatorname{wigner}\left(A, alpha\right))\right)\})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.WPS` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Page 1, the introduction describes WPS as “quantum states with non-negative Wigner function”. Page 3, Section 2 specifies: “We denote by 𝒟⊂ℬ₁ the set of Hermitian positive semi-definite (PSD) operators of unit trace and refer to operators in 𝒟 as states.” Matrix.PosSemidef includes Hermitian symmetry. The finite-matrix set implements these conditions without an additional restriction on phase-space points.

**Definition 1.5 (IsExtremeWPS).**

$$\forall K : \mathbb{N}, (\forall sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), (\operatorname{IsExtremeWPS}\left(K, sigma\right) = \left(sigma \in \operatorname{WPS}\left(K\right) \land \forall x : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), (x \in \operatorname{WPS}\left(K\right) \Rightarrow \forall y : \operatorname{Matrix}\left(\operatorname{Fin}\left(K + 1\right), \operatorname{Fin}\left(K + 1\right), \mathbb{C}\right), (y \in \operatorname{WPS}\left(K\right) \Rightarrow \left(sigma = (\frac{1}{2}) \cdot (x + y) \Rightarrow \left(x = sigma \land y = sigma\right)\right)))\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.IsExtremeWPS` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Page 4, Definition 2: “Given a convex set 𝒞, the point a∈𝒞 is an extreme point of 𝒞 if and only if ∀x,y∈𝒞:a=½(x+y)⇔x=y=a.” Membership and the forward midpoint implication are explicit. The reverse implication is automatic when both endpoints equal sigma.

**Definition 1.6 (bsState).**

$$\forall N : \mathbb{N}, (\forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\forall phi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\operatorname{let} Psi = \operatorname{beamSplitter}\left(\frac{1}{2}, \sum_{j:\operatorname{Fin}\left(N + 1\right)}(\sum_{k:\operatorname{Fin}\left(N + 1\right)}(((psi\left(j\right)) \cdot (phi\left(k\right))) \cdot (\operatorname{fockPair}\left(\operatorname{val}\left(j\right), \operatorname{val}\left(k\right)\right))))\right); \forall m : \operatorname{Fin}\left((2) \cdot (N) + 1\right), (\forall mp : \operatorname{Fin}\left((2) \cdot (N) + 1\right), (\operatorname{bsState}\left(psi, phi\right)\left(m, mp\right) = \operatorname{tsum}\left((ell:\mathbb{N})\mapsto(Psi\left(ell\right)\left(\operatorname{val}\left(m\right)\right)) \cdot (\operatorname{starRingEnd}\left(\mathbb{C}, Psi\left(ell\right)\left(\operatorname{val}\left(mp\right)\right)\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.bsState` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Page 4, Definition 1: “A beam-splitter state σ̂ is the single-mode output of a balanced beam-splitter acting on a separable state ρ̂ₛₑₚ, i.e. σ̂=Tr₂[Û₁/₂ ρ̂ₛₑₚ Û†₁/₂].” Here the separable input is a product of finite pure vectors. The second-mode sum is a tsum over all natural occupations. The repository rotation differs from the paper's by second-mode parity before and after the rotation. Output parity disappears under the partial trace; input parity permutes the finite-Fock pure states and fixes the even-supported inputs used below. Thus the universal question and the counterexample agree with the paper's convention.

**Definition 1.7 (claim).**

$$claim = \forall N : \mathbb{N}, (\forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\forall phi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\sum_{i:\operatorname{Fin}\left(N + 1\right)}((\left\lVert psi\left(i\right) \right\rVert)^{2}) = 1 \Rightarrow \left(\sum_{i:\operatorname{Fin}\left(N + 1\right)}((\left\lVert phi\left(i\right) \right\rVert)^{2}) = 1 \Rightarrow \operatorname{IsExtremeWPS}\left((2) \cdot (N), \operatorname{bsState}\left(psi, phi\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.claim` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

Page 15, Section 6: “This leads us to formulate the following open problem: for any two Fock-bounded pure states |ψ⟩,|φ⟩ is the beamsplitter state σ̂(ψ,φ) an extreme WPS?” N is any natural cutoff; psi and phi are arbitrary complex vectors on Fin (N+1), each with squared norm sum one. The output cutoff is 2*N. A midpoint decomposition in this finite WPS set also disproves extremality in the full WPS set.

**Theorem 1.8 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result` (`✓ std3`). ∎

*Resolves.* `Problems/van-herstraeten-et-al-2025-beam-splitter-state-extremality` (refuted) by `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"van-herstraeten-et-al-2025-beam-splitter-state-extremality","declaration_gid":"D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud (2025). *Extreme non-negative Wigner functions*. URL: <https://arxiv.org/abs/2512.14831v3>.

*Commentary.*

For every positive real a, the inputs (|0>+a|2>)/sqrt(1+a^2) and (|0>-a|2>)/sqrt(1+a^2) give a non-extreme state supported on levels zero through four. After the positive Gaussian factor is removed, the output Wigner polynomial splits as the square of a real radial polynomial plus 32*a^2*Re(alpha)^2*Im(alpha)^2. A perturbation carries just the second square. Subtracting its trace multiple of the output produces a nonzero traceless direction; sufficiently small displacements in both signs remain positive semidefinite and Wigner-positive. Their midpoint is the output state, and the level-four diagonal entry separates the positive endpoint from it. The family at a=1/2 refutes the universal claim. The paper's extremality theorem for two Fock-state inputs and its Vertigo-map results remain compatible with this conclusion.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.IsExtremeWPS`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.WPS`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.bsState`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.genLaguerre`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.wigner`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.wignerFock`
- Dependency: [D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum](../../../Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter](BeamSplitter.md)
