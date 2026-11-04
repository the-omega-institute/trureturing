# Vacuum and one-photon Wigner-majorization chains

## Abstract

Vacuum and one-photon mixtures form two oppositely ordered chains meeting at one half.

**Definition 1.1 (fockWigner).**

$$\forall n : \mathbb{N}, (\forall x : \mathbb{R}, (\forall p : \mathbb{R}, (\operatorname{fockWigner}\left(n, x, p\right) = (((\frac{(-(1))^{n}}{\operatorname{Real}.\operatorname{pi}}) \cdot (\operatorname{Real}.\operatorname{exp}\left(-(((x)^{2}) + ((p)^{2}))\right))) \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{FockAttenuator}.\operatorname{FiniteFockBeamSplitterNonExtremality}.\operatorname{genLaguerre}\left(0, n, (2) \cdot (((x)^{2}) + ((p)^{2}))\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.fockWigner` (`✓ std3`).

*Citation.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Page 16, Eq. (99), gives “W_{|n⟩}(x,p) = ((−1)ⁿ/π) e^{−(x²+p²)} Lₙ(2(x²+p²))”. The polynomial Lₙ is genLaguerre 0 n, with natural occupation n and real phase-space coordinates x and p.

**Definition 1.2 (mixtureWigner).**

$$\forall u : \mathbb{R}, (\forall x : \mathbb{R}, (\forall p : \mathbb{R}, (\operatorname{mixtureWigner}\left(u, x, p\right) = ((((1) - (u)) \cdot (\operatorname{fockWigner}\left(0, x, p\right))) + ((u) \cdot (\operatorname{fockWigner}\left(1, x, p\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.mixtureWigner` (`✓ std3`).

*Citation.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Page 16, Eq. (100): “W̃_u(r) = (1 − u) W_{|0⟩}(r) + u W_{|1⟩}(r)”, with “u ∈ [0, 1]”. The expression is defined for real u; the two chain statements restrict the physical interval.

**Definition 1.3 (levelFunctional).**

$$\forall W : (\mathbb{R} \to (\mathbb{R} \to \mathbb{R})), (\forall t : \mathbb{R}, (\operatorname{levelFunctional}\left(W, t\right) = (\int_{r:\mathbb{R}\times\mathbb{R}} (\operatorname{max}\left((\operatorname{abs}\left(W\left(\operatorname{Prod}.\operatorname{fst}\left(r\right), \operatorname{Prod}.\operatorname{snd}\left(r\right)\right)\right)) - (t), 0\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.levelFunctional` (`✓ std3`).

*Citation.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Page 16, Eq. (97): “I_t[|W_ρ̂|] ≡ ∫ [|W_ρ̂(r)| − t]₊ dr”. The positive part is max with zero and the integral uses product Lebesgue measure on the actual plane.

**Definition 1.4 (WignerMajorizes).**

$$\forall W1 : (\mathbb{R} \to (\mathbb{R} \to \mathbb{R})), (\forall W2 : (\mathbb{R} \to (\mathbb{R} \to \mathbb{R})), (\operatorname{WignerMajorizes}\left(W1, W2\right) = (\forall t : \mathbb{R}, ((0 \le t) \Rightarrow (\operatorname{levelFunctional}\left(W2, t\right) \le \operatorname{levelFunctional}\left(W1, t\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.WignerMajorizes` (`✓ std3`).

*Citation.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Page 16, Result 8: “We define that ρ̂₁ ≻_W ρ̂₂ if and only if |W₁| ≻_w |W₂|”. The threshold formulation in Eq. (98) compares these level functionals for every t ≥ 0. The two mixtures have integrable absolute values.

**Definition 1.5 (claim).**

$$claim = ((\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((\frac{1}{2} \le u) \Rightarrow ((u \le v) \Rightarrow ((v \le 1) \Rightarrow (\operatorname{WignerMajorizes}\left(\operatorname{mixtureWigner}\left(v\right), \operatorname{mixtureWigner}\left(u\right)\right))))))) \land (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((0 \le u) \Rightarrow ((u \le v) \Rightarrow ((v \le \frac{1}{2}) \Rightarrow (\operatorname{WignerMajorizes}\left(\operatorname{mixtureWigner}\left(u\right), \operatorname{mixtureWigner}\left(v\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.claim` (`✓ std3`).

*Citation.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Page 17, Section V.A.1: “By trying for several instances, we may conjecture that there is a majorization order along the family W̃_u only as long as u > 1/2.” “It would be interesting to understand this observation better analytically. We leave this question for future works.” The proposition specifies increasing order on [1/2,1] and decreasing order on [0,1/2], including both endpoints.

**Theorem 1.6 (result).**

$$(\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((\frac{1}{2} \le u) \Rightarrow ((u \le v) \Rightarrow ((v \le 1) \Rightarrow (\operatorname{WignerMajorizes}\left(\operatorname{mixtureWigner}\left(v\right), \operatorname{mixtureWigner}\left(u\right)\right))))))) \land (\forall u : \mathbb{R}, (\forall v : \mathbb{R}, ((0 \le u) \Rightarrow ((u \le v) \Rightarrow ((v \le \frac{1}{2}) \Rightarrow (\operatorname{WignerMajorizes}\left(\operatorname{mixtureWigner}\left(u\right), \operatorname{mixtureWigner}\left(v\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result` (`✓ std3`). ∎

*Resolves.* `Problems/de-boer-di-giulio-keski-vakkuri-tonni-2024-wigner-majorization-chains` (proved) by `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"de-boer-di-giulio-keski-vakkuri-tonni-2024-wigner-majorization-chains","declaration_gid":"D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

Both intervals form chains for every nonnegative threshold. Polar integration identifies the level functional with the affine family h+c*h′, where h(s)=s*exp(−s), c=1−2*u and T=pi*t. Derivative cancellation gives a convex minimum at c=0. The two monotone rays give the opposite directions on the two parameter intervals. Strictness and complete comparisons between the intervals remain separate questions.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.WignerMajorizes`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.fockWigner`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.levelFunctional`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.mixtureWigner`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization.result`
- Dependency: [D5/S3/Analytic/Convexity/DerivativeHingeMajorization](../../../Analytic/Convexity/DerivativeHingeMajorization.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality](FiniteFockBeamSplitterNonExtremality.md)
