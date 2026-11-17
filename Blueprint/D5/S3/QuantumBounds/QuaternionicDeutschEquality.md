# Quaternionic Deutsch equality

## Abstract

Lower Deutsch equality for quaternionic continuous Parseval frames is equivalent to rank-one rigidity and implies simultaneous equality.

**Definition 1.1 (Right quaternionic inner product).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \operatorname{RightHilbert}\left(Q\right) := \{inner : Q \to \left(Q \to \operatorname{Quaternion}\left(\mathbb{R}\right)\right); (\forall (x : Q), inner\left(x, x\right) = (\operatorname{Quaternion}.\operatorname{re}\left(inner\left(x, x\right)\right) : \operatorname{Quaternion}\left(\mathbb{R}\right))) \land ((\forall (x : Q), 0 \le \operatorname{Quaternion}.\operatorname{re}\left(inner\left(x, x\right)\right)) \land ((\forall (x : Q), (inner\left(x, x\right) = 0) \Rightarrow (x = 0)) \land ((\forall (x : Q), \forall (y : Q), \forall (z : Q), inner\left(x + y, z\right) = inner\left(x, z\right) + inner\left(y, z\right)) \land ((\forall (x : Q), \forall (y : Q), \forall (q : \operatorname{Quaternion}\left(\mathbb{R}\right)), inner\left(x, \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{MulOpposite}.\operatorname{op}\left(q\right), y\right)\right) = inner\left(x, y\right) \cdot q) \land ((\forall (x : Q), \forall (y : Q), inner\left(x, y\right) = \operatorname{star}\left(inner\left(y, x\right)\right)) \land (\forall (x : Q), \operatorname{norm}\left(x\right) = \operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Quaternion}.\operatorname{re}\left(inner\left(x, x\right)\right)\right)))))))\}$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.RightHilbert` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Definition 1.9, printed pages 4–5: “A right quaternionic vector space 𝒬 over ℍ is said to be a (right) quaternionic Hilbert space if there exists a map (called as quaternionic inner product) ⟨·, ·⟩: 𝒬 × 𝒬 → ℍ such that the following hold.” The record gives all inner-product fields; completeness is a separate CompleteSpace hypothesis in the classification. Right scalar multiplication by q is (MulOpposite.op q) • x. The displayed record lists its inner map and all seven laws.

**Definition 1.2 (Continuous Parseval frame).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (tau : Omega \to Q), \operatorname{ContinuousParseval}\left(h, mu, tau\right) = ((\forall (x : Q), \operatorname{Measurable}\left(\lambda (alpha : Omega) \mapsto \operatorname{RightHilbert}.\operatorname{inner}\left(h, tau\left(alpha\right), x\right)\right)) \land (\forall (x : Q), \operatorname{MeasureTheory}.\operatorname{lintegral}\left(mu, \lambda (alpha : Omega) \mapsto \operatorname{ENNReal}.\operatorname{ofReal}\left((\operatorname{norm}\left(\operatorname{RightHilbert}.\operatorname{inner}\left(h, tau\left(alpha\right), x\right)\right))^{2}\right)\right) = \operatorname{ENNReal}.\operatorname{ofReal}\left((\operatorname{norm}\left(x\right))^{2}\right)))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.ContinuousParseval` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Definition 2.7, printed page 10: “Let (Ω, μ) be a measure space. A collection {τα}α∈Ω in a quaternionic Hilbert space 𝒬 is said to be a continuous Parseval frame for 𝒬 if the following conditions hold.” “For each x ∈ 𝒬, the map Ω ∋ α ↦ ⟨τα, x⟩ ∈ ℍ is measurable.” Its second condition is ‖x‖² = ∫Ω |⟨τα, x⟩|² dμ(α) for every x. Quaternionic coefficients use the Borel measurable space. The nonnegative extended integral retains divergent values.

**Definition 1.3 (Pointwise norm bound).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], \forall (Omega : Type), \forall (tau : Omega \to Q), \operatorname{OneBounded}\left(tau\right) = (\forall (alpha : Omega), \operatorname{norm}\left(tau\left(alpha\right)\right) \le 1)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.OneBounded` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Definition 2.8, printed page 10: “A continuous Parseval frame {τα}α∈Ω for 𝒬 is said to be 1-bounded if” ‖τα‖ ≤ 1, ∀ α ∈ Ω. This includes indices of measure zero.

**Definition 1.4 (Everywhere nonzero coefficients).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (tau : Omega \to Q), \operatorname{EntropyDomain}\left(h, tau\right) = \operatorname{setOf}\left(\lambda (x : Q) \mapsto \forall (alpha : Omega), \operatorname{RightHilbert}.\operatorname{inner}\left(h, tau\left(alpha\right), x\right) \ne 0\right)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.EntropyDomain` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Printed page 10: 𝒬τ ≔ {x ∈ 𝒬: ⟨τα, x⟩ ≠ 0, ∀ α ∈ Ω}. Membership requires a nonzero coefficient at every index.

**Definition 1.5 (Right normalization).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (x : Q), \operatorname{unitVector}\left(x\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{MulOpposite}.\operatorname{op}\left(((\operatorname{norm}\left(x\right))^{-(1)} : \operatorname{Quaternion}\left(\mathbb{R}\right))\right), x\right)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.unitVector` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Section 2, printed page 5, states: “by x/r, we mean x r⁻¹.” Here r is the nonzero real norm of the state; its inverse is coerced to Quaternion ℝ before MulOpposite.op acts on the vector.

**Definition 1.6 (Squared normalized coefficient).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (tau : Omega \to Q), \forall (x : Q), \forall (alpha : Omega), \operatorname{density}\left(h, tau, x, alpha\right) = (\operatorname{norm}\left(\operatorname{RightHilbert}.\operatorname{inner}\left(h, tau\left(alpha\right), \operatorname{unitVector}\left(x\right)\right)\right))^{2}$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.density` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

The coefficient density appearing in the continuous Shannon formula is the squared norm of the quaternionic inner product with the normalized state.

**Definition 1.7 (Continuous Shannon entropy).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (tau : Omega \to Q), \forall (x : Q), \operatorname{entropy}\left(h, mu, tau, x\right) = \operatorname{MeasureTheory}.\operatorname{lintegral}\left(mu, \lambda (alpha : Omega) \mapsto \operatorname{ENNReal}.\operatorname{ofReal}\left(-(\operatorname{density}\left(h, tau, x, alpha\right)) \cdot \operatorname{Real}.\operatorname{log}\left(\operatorname{density}\left(h, tau, x, alpha\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.entropy` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Printed page 10: “Given a continuous 1-bounded Parseval frame {τα}α∈Ω for 𝒬, we define the continuous Shannon entropy at a point x ∈ 𝒬τ as” Sτ(x) ≔ −∫Ω |⟨τα, x/‖x‖⟩|² log |⟨τα, x/‖x‖⟩|² dμ(α) ≥ 0. The natural logarithm and the extended nonnegative integral retain possible infinite entropy.

**Definition 1.8 (Pointwise cross supremum).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), \forall (Delta : Type), \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), \operatorname{overlap}\left(h, tau, omega\right) = \operatorname{sSup}\left(\operatorname{Set}.\operatorname{range}\left(\lambda (z : \operatorname{Prod}\left(Omega, Delta\right)) \mapsto \operatorname{norm}\left(\operatorname{RightHilbert}.\operatorname{inner}\left(h, tau\left(\operatorname{Prod}.\operatorname{fst}\left(z\right)\right), omega\left(\operatorname{Prod}.\operatorname{snd}\left(z\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.overlap` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

The supremum in Theorem 2.9, equation (11), printed page 11, ranges over every pair of indices. It is the actual real supremum rather than an essential supremum.

**Definition 1.9 (Deutsch lower endpoint).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), \forall (Delta : Type), \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), \operatorname{deutschEndpoint}\left(h, tau, omega\right) = \operatorname{ENNReal}.\operatorname{ofReal}\left(-(2) \cdot \operatorname{Real}.\operatorname{log}\left(\frac{1 + \operatorname{overlap}\left(h, tau, omega\right)}{2}\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.deutschEndpoint` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

The central lower endpoint in equation (11), printed page 11, is minus twice the natural logarithm of (1 + overlap)/2, embedded into ENNReal.

**Definition 1.10 (Equality at the lower endpoint).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], \forall (Delta : Type), [\operatorname{MeasurableSpace}\left(Delta\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), \forall (x : Q), \operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right) = (\operatorname{entropy}\left(h, mu, tau, x\right) + \operatorname{entropy}\left(h, nu, omega, x\right) = \operatorname{deutschEndpoint}\left(h, tau, omega\right))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.lowerEquality` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

The sum of the two entropies equals the central Deutsch endpoint from equation (11).

**Definition 1.11 (Rank-one rigidity).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], \forall (Delta : Type), [\operatorname{MeasurableSpace}\left(Delta\right)], \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), \operatorname{rigid}\left(mu, nu, tau, omega\right) = ((\operatorname{Module}.\operatorname{rank}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right) = 1) \land ((\operatorname{Filter}.\operatorname{Eventually}\left(\lambda (alpha : Omega) \mapsto \operatorname{norm}\left(tau\left(alpha\right)\right) = 1, \operatorname{MeasureTheory}.\operatorname{ae}\left(mu\right)\right)) \land (\operatorname{Filter}.\operatorname{Eventually}\left(\lambda (beta : Delta) \mapsto \operatorname{norm}\left(omega\left(beta\right)\right) = 1, \operatorname{MeasureTheory}.\operatorname{ae}\left(nu\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.rigid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

The space has quaternionic rank one, and both frame families have unit norm almost everywhere with respect to their own measures.

**Definition 1.12 (Simultaneous equality).**

$$\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \forall (Omega : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], \forall (Delta : Type), [\operatorname{MeasurableSpace}\left(Delta\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), \forall (x : Q), \operatorname{simultaneousEquality}\left(h, mu, nu, tau, omega, x\right) = ((mu\left(\operatorname{Set}.\operatorname{univ}\right) = 1) \land ((nu\left(\operatorname{Set}.\operatorname{univ}\right) = 1) \land ((\operatorname{overlap}\left(h, tau, omega\right) = 1) \land ((\operatorname{entropy}\left(h, mu, tau, x\right) = 0) \land (\operatorname{entropy}\left(h, nu, omega, x\right) = 0)))))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.simultaneousEquality` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Both total masses and the pointwise overlap equal one, and both entropies vanish. Thus every endpoint of equation (11) equals zero.

**Definition 1.13 (A nonvacuous equality model).**

$$\operatorname{equalityModelExists} = (\exists (Q : Type), \exists [\operatorname{NormedAddCommGroup}\left(Q\right)], \exists [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], \exists [\operatorname{CompleteSpace}\left(Q\right)], \exists (h : \operatorname{RightHilbert}\left(Q\right)), \exists (Omega : Type), \exists (Delta : Type), \exists [\operatorname{MeasurableSpace}\left(Omega\right)], \exists [\operatorname{MeasurableSpace}\left(Delta\right)], \exists (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \exists (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \exists (tau : Omega \to Q), \exists (omega : Delta \to Q), \exists (x : Q), (\operatorname{ContinuousParseval}\left(h, mu, tau\right)) \land ((\operatorname{ContinuousParseval}\left(h, nu, omega\right)) \land ((\operatorname{OneBounded}\left(tau\right)) \land ((\operatorname{OneBounded}\left(omega\right)) \land ((x \ne 0) \land ((x \in \operatorname{EntropyDomain}\left(h, tau\right)) \land ((x \in \operatorname{EntropyDomain}\left(h, omega\right)) \land (\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right)))))))))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.equalityModelExists` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

There exist a complete right quaternionic space, two continuous Parseval frames of norm at most one, and a nonzero state with everywhere nonzero coefficients and lower equality. The proof constructs the ULift quaternionic line and singleton Dirac index spaces at arbitrary universes.

**Definition 1.14 (Question 2.12 and the classification).**

$$\operatorname{claim} = ((\operatorname{equalityModelExists}) \land (\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], [\operatorname{CompleteSpace}\left(Q\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (Omega : Type), \forall (Delta : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], [\operatorname{MeasurableSpace}\left(Delta\right)], \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), (\operatorname{ContinuousParseval}\left(h, mu, tau\right)) \Rightarrow ((\operatorname{ContinuousParseval}\left(h, nu, omega\right)) \Rightarrow ((\operatorname{OneBounded}\left(tau\right)) \Rightarrow ((\operatorname{OneBounded}\left(omega\right)) \Rightarrow ((\forall (x : Q), (x \ne 0) \Rightarrow ((x \in \operatorname{EntropyDomain}\left(h, tau\right)) \Rightarrow ((x \in \operatorname{EntropyDomain}\left(h, omega\right)) \Rightarrow (((\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right)) \Leftrightarrow (\operatorname{rigid}\left(mu, nu, tau, omega\right))) \land ((\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right)) \Rightarrow (\operatorname{simultaneousEquality}\left(h, mu, nu, tau, omega, x\right))))))) \land ((\exists (x : Q), (x \ne 0) \land ((x \in \operatorname{EntropyDomain}\left(h, tau\right)) \land ((x \in \operatorname{EntropyDomain}\left(h, omega\right)) \land (\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right))))) \Leftrightarrow ((\operatorname{rigid}\left(mu, nu, tau, omega\right)) \land ((\forall (alpha : Omega), tau\left(alpha\right) \ne 0) \land (\forall (beta : Delta), omega\left(beta\right) \ne 0))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/QuaternionicDeutschEquality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Question 2.12, printed page 12, asks verbatim: “Let (Ω, μ), (Δ, ν) be measure spaces, 𝒬 be a quaternionic Hilbert space. For which pairs of 1-bounded continuous Parseval frames {τα}α∈Ω and {ωβ}β∈Δ for 𝒬, we have equality in Inequality (11)?” Q is a right module over MulOpposite (Quaternion ℝ), h is its inner-product record, and the two index spaces have arbitrary measures. The answer classifies the central lower equality for each nonzero state in both entropy domains and then classifies existence of such a state for the pair. Completeness is retained. The upper link alone is outside this statement.

**Theorem 1.15 (Lower equality is rigid and simultaneous).**

$$(\operatorname{equalityModelExists}) \land (\forall (Q : Type), [\operatorname{NormedAddCommGroup}\left(Q\right)], [\operatorname{Module}\left(\operatorname{MulOpposite}\left(\operatorname{Quaternion}\left(\mathbb{R}\right)\right), Q\right)], [\operatorname{CompleteSpace}\left(Q\right)], \forall (h : \operatorname{RightHilbert}\left(Q\right)), \forall (Omega : Type), \forall (Delta : Type), [\operatorname{MeasurableSpace}\left(Omega\right)], [\operatorname{MeasurableSpace}\left(Delta\right)], \forall (mu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Omega\right)), \forall (nu : \operatorname{MeasureTheory}.\operatorname{Measure}\left(Delta\right)), \forall (tau : Omega \to Q), \forall (omega : Delta \to Q), (\operatorname{ContinuousParseval}\left(h, mu, tau\right)) \Rightarrow ((\operatorname{ContinuousParseval}\left(h, nu, omega\right)) \Rightarrow ((\operatorname{OneBounded}\left(tau\right)) \Rightarrow ((\operatorname{OneBounded}\left(omega\right)) \Rightarrow ((\forall (x : Q), (x \ne 0) \Rightarrow ((x \in \operatorname{EntropyDomain}\left(h, tau\right)) \Rightarrow ((x \in \operatorname{EntropyDomain}\left(h, omega\right)) \Rightarrow (((\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right)) \Leftrightarrow (\operatorname{rigid}\left(mu, nu, tau, omega\right))) \land ((\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right)) \Rightarrow (\operatorname{simultaneousEquality}\left(h, mu, nu, tau, omega, x\right))))))) \land ((\exists (x : Q), (x \ne 0) \land ((x \in \operatorname{EntropyDomain}\left(h, tau\right)) \land ((x \in \operatorname{EntropyDomain}\left(h, omega\right)) \land (\operatorname{lowerEquality}\left(h, mu, nu, tau, omega, x\right))))) \Leftrightarrow ((\operatorname{rigid}\left(mu, nu, tau, omega\right)) \land ((\forall (alpha : Omega), tau\left(alpha\right) \ne 0) \land (\forall (beta : Delta), omega\left(beta\right) \ne 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/QuaternionicDeutschEquality.result` (`✓ std3`). ∎

*Resolves.* `Problems/quaternionic-deutsch` (proved) by `D5/S3/QuantumBounds/QuaternionicDeutschEquality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"quaternionic-deutsch","declaration_gid":"D5/S3/QuantumBounds/QuaternionicDeutschEquality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2026). *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*. DOI: [10.48550/arXiv.2610.35881](https://doi.org/10.48550/arXiv.2610.35881). URL: <https://arxiv.org/abs/2610.35881v1>.

*Commentary.*

Quaternionic Buzano bounds the product of the two coefficient densities. Actual bounded suprema give entropy decompositions with nonnegative remainder integrals. Equality makes both densities constant almost everywhere. Parseval at saturated frame vectors identifies both constants as the squared overlap; the scalar identity forces overlap one. Parseval applied to an orthogonal residual then forces rank one. Conversely, rank one and unit frame norms almost everywhere give both masses one and both entropies zero. Pair existence also requires every frame vector to be nonzero, including null indices. No product-measure sigma-finiteness assumption or finite total mass is imposed.

## References

- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.ContinuousParseval`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.EntropyDomain`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.OneBounded`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.RightHilbert`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.claim`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.density`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.deutschEndpoint`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.entropy`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.equalityModelExists`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.lowerEquality`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.overlap`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.result`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.rigid`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.simultaneousEquality`
- Truth anchor: `D5/S3/QuantumBounds/QuaternionicDeutschEquality.unitVector`
