# Spin-one rotation correlations with finitely many outcomes

## Abstract

Every normalized degree-two rotation family has a single quantum realization.

**Definition 1.1 (QuantumSpinOne).**

$$\forall (A : Type) , [\operatorname{Fintype}\left(A\right)] , \forall (p : A \to \left(\mathbb{R} \to \mathbb{R}\right)) , \operatorname{QuantumSpinOne}\left(p\right) = (\exists (multiplicity : \operatorname{Fin}\left(3\right) \to \mathbb{N}) , \exists (rho : \operatorname{DensityState}\left((\Sigma (j : \operatorname{Fin}\left(3\right)) , \operatorname{Fin}\left(multiplicity (j)\right))\right)) , \exists (E : A \to \operatorname{Matrix}\left((\Sigma (j : \operatorname{Fin}\left(3\right)) , \operatorname{Fin}\left(multiplicity (j)\right)), (\Sigma (j : \operatorname{Fin}\left(3\right)) , \operatorname{Fin}\left(multiplicity (j)\right)), \mathbb{C}\right)) , ((\forall (a : A) , \operatorname{Matrix}.\operatorname{PosSemidef} (E (a))) \land (\sum (a : A) , E (a) = 1)) \land (\forall (a : A) , \forall (theta : \mathbb{R}) , \operatorname{Matrix}.\operatorname{trace} (\operatorname{Matrix}.\operatorname{diagonal} (\lambda (i : (\Sigma (j : \operatorname{Fin}\left(3\right)) , \operatorname{Fin}\left(multiplicity (j)\right))) \mapsto \operatorname{Complex}.\operatorname{exp} (\operatorname{Complex}.\operatorname{I} \cdot (\left((\operatorname{val}\left(\operatorname{Sigma}.\operatorname{fst} (i)\right) : \mathbb{R}) - 1\right) \cdot theta : \mathbb{C}))) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.\operatorname{symm} (\operatorname{val}\left(rho\right)) \cdot \operatorname{Matrix}.\operatorname{conjTranspose} (\operatorname{Matrix}.\operatorname{diagonal} (\lambda (i : (\Sigma (j : \operatorname{Fin}\left(3\right)) , \operatorname{Fin}\left(multiplicity (j)\right))) \mapsto \operatorname{Complex}.\operatorname{exp} (\operatorname{Complex}.\operatorname{I} \cdot (\left((\operatorname{val}\left(\operatorname{Sigma}.\operatorname{fst} (i)\right) : \mathbb{R}) - 1\right) \cdot theta : \mathbb{C})))) \cdot E (a)) = (p (a) (theta) : \mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.QuantumSpinOne` (`✓ std3`).

*Citation.* Albert Aloy; Thomas D. Galley; Caroline L. Jones; Stefan L. Ludescher; Markus P. Müller (2024). *Spin-Bounded Correlations — Rotation Boxes Within and Beyond Quantum Theory*. DOI: [10.1007/s00220-024-05123-2](https://doi.org/10.1007/s00220-024-05123-2). URL: <https://arxiv.org/abs/2312.09278v2>.

*Commentary.*

Equation (4), page 7: “Note that the integers nⱼ in Eq. (4) can be arbitrary finite numbers, and so there is no a priori upper bound on the Hilbert space dimension on which the rotation box is represented.” The sigma type gives multiplicities of the three frequencies −1, 0, 1. Definition 1, page 7: “such that there exists a Hilbert space with a projective representation of SO(2) of the form (4), some quantum state (i.e. density matrix) ρ, and a POVM {Eₐ}ₐ∈𝒜 on that Hilbert space such that” P(a|θ) = Tr(UθρUθ†Eₐ). One density state and one measurement serve every real angle and every outcome. DensityState is the finite-dimensional complex density-state type; the two displayed conditions on E say that its effects are positive semidefinite and sum to the identity. The complex trace equals the real probability embedded in ℂ.

**Definition 1.2 (RotationSpinOne).**

$$\forall (A : Type) , [\operatorname{Fintype}\left(A\right)] , \forall (p : A \to \left(\mathbb{R} \to \mathbb{R}\right)) , \operatorname{RotationSpinOne}\left(p\right) = \left((\exists (cZero : A \to \mathbb{R}) , \exists (cOne : A \to \mathbb{R}) , \exists (sOne : A \to \mathbb{R}) , \exists (cTwo : A \to \mathbb{R}) , \exists (sTwo : A \to \mathbb{R}) , \forall (a : A) , \forall (theta : \mathbb{R}) , p (a) (theta) = cZero (a) + cOne (a) \cdot \operatorname{Real}.\operatorname{cos} (theta) + sOne (a) \cdot \operatorname{Real}.\operatorname{sin} (theta) + cTwo (a) \cdot \operatorname{Real}.\operatorname{cos} (2 \cdot theta) + sTwo (a) \cdot \operatorname{Real}.\operatorname{sin} (2 \cdot theta)) \land ((\forall (a : A) , \forall (theta : \mathbb{R}) , (0 \le p (a) (theta)) \land (p (a) (theta) \le 1)) \land (\forall (theta : \mathbb{R}) , \sum (a : A) , p (a) (theta) = 1))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.RotationSpinOne` (`✓ std3`).

*Citation.* Albert Aloy; Thomas D. Galley; Caroline L. Jones; Stefan L. Ludescher; Markus P. Müller (2024). *Spin-Bounded Correlations — Rotation Boxes Within and Beyond Quantum Theory*. DOI: [10.1007/s00220-024-05123-2](https://doi.org/10.1007/s00220-024-05123-2). URL: <https://arxiv.org/abs/2312.09278v2>.

*Commentary.*

Definition 2, page 9: “such that every one of the functions is a trigonometric polynomial of degree at most 2J in θ, and 0 ≤ P(a|θ) ≤ 1 as well as ∑ₐ∈𝒜 P(a|θ) = 1 for all θ.” The displayed expression specializes J to 1 and uses the real Fourier coefficients of Lemma 5. The five coefficient functions have the same finite outcome index A; every probability bound and the sum identity hold at every real angle.

**Definition 1.3 (claim).**

$$claim = (\forall (A : Type) , [\operatorname{Fintype}\left(A\right)] , 3 \le \operatorname{Fintype}.\operatorname{card} (A) \Rightarrow \forall (p : A \to \left(\mathbb{R} \to \mathbb{R}\right)) , \operatorname{QuantumSpinOne}\left(p\right) \Leftrightarrow \operatorname{RotationSpinOne}\left(p\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.claim` (`✓ std3`).

*Citation.* Albert Aloy; Thomas D. Galley; Caroline L. Jones; Stefan L. Ludescher; Markus P. Müller (2024). *Spin-Bounded Correlations — Rotation Boxes Within and Beyond Quantum Theory*. DOI: [10.1007/s00220-024-05123-2](https://doi.org/10.1007/s00220-024-05123-2). URL: <https://arxiv.org/abs/2312.09278v2>.

*Commentary.*

Section 4.2.3, page 17: “Hence, even though the set of spin correlations ℛ₁ and 𝒬₁ agree, the corresponding GPT systems have genuinely different information-theoretic and physical behaviors. This is also the reason why we do not currently know whether 𝒬₁ᴬ = ℛ₁ᴬ for |𝒜| ≥ 3.” The proposition asserts this equality for every finite type A with at least three elements and every real probability family p. Multiplicities in the quantum realization are arbitrary finite natural numbers.

**Theorem 1.4 (result).**

$$\forall (A : Type) , [\operatorname{Fintype}\left(A\right)] , 3 \le \operatorname{Fintype}.\operatorname{card} (A) \Rightarrow \forall (p : A \to \left(\mathbb{R} \to \mathbb{R}\right)) , \operatorname{QuantumSpinOne}\left(p\right) \Leftrightarrow \operatorname{RotationSpinOne}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Albert Aloy; Thomas D. Galley; Caroline L. Jones; Stefan L. Ludescher; Markus P. Müller (2024). *Spin-Bounded Correlations — Rotation Boxes Within and Beyond Quantum Theory*. DOI: [10.1007/s00220-024-05123-2](https://doi.org/10.1007/s00220-024-05123-2). URL: <https://arxiv.org/abs/2312.09278v2>.

*Commentary.*

Every nonnegative degree-two trigonometric polynomial has a positive semidefinite three-by-three Gram representative. Averaging each representative with its reversal transpose preserves its polynomial. Probability normalization forces the sum of these averaged matrices to be diagonal with trace one. Taking inverse square roots on the nonzero diagonal support, and distributing the complementary identity equally among the outcomes, gives one complete measurement. Square roots of the diagonal entries give a pure density state, using one copy of each frequency. Conversely, the finite-multiplicity Born trace has only the five frequency differences −2, −1, 0, 1, 2. The state may depend on the family; the statement supplies no common embedding of the entire general probabilistic theory.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.QuantumSpinOne`
- Truth anchor: `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.RotationSpinOne`
- Truth anchor: `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../../Foundation/FiniteStateChannel.md)
