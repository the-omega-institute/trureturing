# Passive bosonic Fock model

## Abstract

Finite-mode bosonic Fock space, exponential vectors and passive evolution.

**Definition 1.1 (Hilbert).**

$$\operatorname{Hilbert} = \{Carrier:\operatorname{Type};normed:\operatorname{NormedAddCommGroup}\left(Carrier\right);inner:\operatorname{InnerProductSpace}\left(\mathbb{C}, Carrier\right);complete:\operatorname{CompleteSpace}\left(Carrier\right)\}$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.Hilbert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

A Hilbert record consists of its carrier, a normed additive group, a compatible complex inner product and completeness. The last two fields use the normed structure; all three structure fields are instances.

**Definition 1.2 (hilbertStep).**

$$\forall (H : \operatorname{Hilbert}), (\operatorname{hilbertStep}\left(H\right) = \operatorname{Hilbert.mk}\left(\operatorname{lp}\left(\operatorname{Function.const}\left(\mathbb{N}, \operatorname{H.Carrier}\right), 2\right), \operatorname{inferInstance}, \operatorname{inferInstance}, \operatorname{inferInstance}\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.hilbertStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The next Hilbert space is the square-summable sequence space over H.Carrier. The other three fields use their inherited instances.

**Definition 1.3 (fockHilbert).**

$$\begin{aligned}\operatorname{fockHilbert}\left(0\right) = \operatorname{Hilbert.mk}\left(\mathbb{C}, \operatorname{inferInstance}, \operatorname{inferInstance}, \operatorname{inferInstance}\right)\\\forall (k : \mathbb{N}), (\operatorname{fockHilbert}\left(k + 1\right) = \operatorname{hilbertStep}\left(\operatorname{fockHilbert}\left(k\right)\right))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.fockHilbert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The zero-mode carrier is the complex field. Adding a mode adds one unbounded square-summable occupation coordinate. The constructor at zero carries the usual complex Hilbert structures.

**Definition 1.4 (Fock).**

$$\forall (k : \mathbb{N}), (\operatorname{Fock}\left(k\right) = \operatorname{Hilbert.Carrier}\left(\operatorname{fockHilbert}\left(k\right)\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.Fock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The k-mode carrier is the Carrier field of fockHilbert k.

**Definition 1.5 (Modes).**

$$\forall (k : \mathbb{N}), (\operatorname{Modes}\left(k\right) = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k\right)\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.Modes` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Mode amplitudes form the complex Euclidean space on Fin k.

**Definition 1.6 (Passive).**

$$\forall (k : \mathbb{N}), (\operatorname{Passive}\left(k\right) = \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{Modes}\left(k\right), \operatorname{Modes}\left(k\right)\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.Passive` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

A passive network is a complex-linear isometric equivalence of the mode space.

**Definition 1.7 (tail).**

$$\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k + 1\right)), (\operatorname{tail}\left(beta\right) = \operatorname{WithLp.toLp}\left(2, (i : \operatorname{Fin}\left(k\right)) \mapsto (beta\left(\operatorname{Fin.succ}\left(i\right)\right))\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.tail` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The tail discards the first mode.

**Definition 1.8 (headTensor).**

$$\forall (H : \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{NormedSpace}\left(\mathbb{C}, H\right)] \forall (u : \operatorname{lp}\left(\operatorname{Function.const}\left(\mathbb{N}, \mathbb{C}\right), 2\right)), (\forall (v : H), (\operatorname{headTensor}\left(u, v\right) = \operatorname{Subtype.mk}\left((n : \mathbb{N}) \mapsto ((u\left(n\right)) \cdot (v))\right))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.headTensor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The nth coordinate is u n times v. Square summability supplies the omitted membership proof.

**Definition 1.9 (exponential).**

$$\begin{aligned}\forall (beta : \operatorname{Modes}\left(0\right)), (\operatorname{exponential}\left(0, beta\right) = (1 : \mathbb{C}))\\\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k + 1\right)), (\operatorname{exponential}\left(k + 1, beta\right) = \operatorname{headTensor}\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector}\left(beta\left(0\right)\right), \operatorname{exponential}\left(k, \operatorname{tail}\left(beta\right)\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.exponential` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The exponential vector is the recursive product of the one-mode exponential vectors with coefficients alpha^n/sqrt(n!).

**Definition 1.10 (coherent).**

$$\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{coherent}\left(k, beta\right) = ((\operatorname{Real.exp}\left(\frac{-(\left\lVert beta \right\rVert)^{2}}{2}\right) : \mathbb{C})) \cdot (\operatorname{exponential}\left(k, beta\right))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.coherent` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Eq. (6) normalizes the exponential vector by exp(-norm(beta)^2/2).

**Definition 1.11 (gamma).**

$$\forall (k : \mathbb{N}), (\forall (V : \operatorname{Passive}\left(k\right)), (\operatorname{gamma}\left(V\right) = \operatorname{LinearEquiv.extendOfIsometry}\left(\operatorname{LinearEquiv.refl}\left(\mathbb{C}, \operatorname{Finsupp}\left(\operatorname{Modes}\left(k\right), \mathbb{C}\right)\right), \operatorname{Finsupp.linearCombination}\left(\mathbb{C}, (beta : \operatorname{Modes}\left(k\right)) \mapsto (\operatorname{exponential}\left(k, beta\right))\right), \operatorname{Finsupp.linearCombination}\left(\mathbb{C}, (beta : \operatorname{Modes}\left(k\right)) \mapsto (\operatorname{exponential}\left(k, V\left(beta\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The identity on finitely supported coefficient functions extends along the two linearCombination maps. Density and preservation of norms establish the omitted proof arguments. This defines a unitary on the completed space.

**Definition 1.12 (NumberDomain).**

$$\forall (k : \mathbb{N}), (\forall (psi : \operatorname{Fock}\left(k + 1\right)), (\operatorname{NumberDomain}\left(psi\right) = \operatorname{Mem\ell p}\left((n : \mathbb{N}) \mapsto (((n : \mathbb{C})) \cdot (psi\left(n\right))), 2\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.NumberDomain` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The weighted coordinates n times psi n must be square summable.

**Definition 1.13 (number).**

$$\forall (k : \mathbb{N}), (\forall (psi : \operatorname{Fock}\left(k + 1\right)), (\forall (h : \operatorname{NumberDomain}\left(psi\right)), (\operatorname{number}\left(psi, h\right) = \operatorname{Subtype.mk}\left((n : \mathbb{N}) \mapsto (((n : \mathbb{C})) \cdot (psi\left(n\right))), h\right))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.number` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The unbounded number operator multiplies the nth coordinate by n; h is its membership proof.

**Definition 1.14 (numberExponential).**

$$\forall (alpha : \mathbb{C}), (\operatorname{numberExponential}\left(alpha\right) = \operatorname{Subtype.mk}\left((n : \mathbb{N}) \mapsto (((n : \mathbb{C})) \cdot (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff}\left(alpha, n\right)))\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.numberExponential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The one-mode exponential vector after number insertion has coordinates n times exponentialCoeff alpha n.

**Definition 1.15 (numberProjector).**

$$\forall (k : \mathbb{N}), (\forall (m : \mathbb{N}), (\operatorname{numberProjector}\left(m\right) = \operatorname{ContinuousLinearMap.comp}\left(\operatorname{lp.singleContinuousLinearMap}\left(\mathbb{C}, \operatorname{Function.const}\left(\mathbb{N}, \operatorname{Fock}\left(k\right)\right), 2, m\right), \operatorname{lp.evalCLM}\left(\mathbb{C}, \operatorname{Function.const}\left(\mathbb{N}, \operatorname{Fock}\left(k\right)\right), 2, m\right)\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.numberProjector` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The bounded projector extracts coordinate m and inserts it at m, acting as the identity on all ignored modes.

**Definition 1.16 (vacuum).**

$$\forall (k : \mathbb{N}), (\operatorname{vacuum}\left(k\right) = \operatorname{exponential}\left(k, 0\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.vacuum` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Vacuum is the exponential vector with zero amplitude.

**Definition 1.17 (onePhoton).**

$$\begin{aligned}\forall (beta : \operatorname{Modes}\left(0\right)), (\operatorname{onePhoton}\left(0, beta\right) = (0 : \mathbb{C}))\\\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k + 1\right)), (\operatorname{onePhoton}\left(k + 1, beta\right) = \operatorname{lp.single}\left(2, 1, (beta\left(0\right)) \cdot (\operatorname{vacuum}\left(k\right))\right) + \operatorname{lp.single}\left(2, 0, \operatorname{onePhoton}\left(k, \operatorname{tail}\left(beta\right)\right)\right)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.onePhoton` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The one-photon embedding separates the first occupied mode from the tail.

**Definition 1.18 (resolvedProbability).**

$$\forall (k : \mathbb{N}), (\forall (m : \mathbb{N}), (\forall (psi : \operatorname{Fock}\left(k + 1\right)), (\operatorname{resolvedProbability}\left(m, psi\right) = (\left\lVert psi\left(m\right) \right\rVert)^{2})))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.resolvedProbability` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The squared norm of the mth component retains the whole vector on the ignored modes.

**Definition 1.19 (effectWeight).**

$$\forall (H : \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall (A : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, H, H\right)), (\forall (B : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, H, H\right)), (\forall (E : \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), H, H\right)), (\forall (psi : H), (\operatorname{effectWeight}\left(A, B, E, psi\right) = \operatorname{inner}\left(\mathbb{C}, B\left(A\left(psi\right)\right), E\left(B\left(A\left(psi\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.effectWeight` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Eq. (2) pairs the final state with the postselection effect. The complex conditional value divides the inserted-state numerator by the nonzero effect weight.

**Definition 1.20 (generalizedWeakValue).**

$$\forall (H : \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall (A : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, H, H\right)), (\forall (B : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, H, H\right)), (\forall (E : \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), H, H\right)), (\forall (psi : H), (\forall (inserted : H), (\forall (h : \operatorname{effectWeight}\left(A, B, E, psi\right) \ne 0), (\operatorname{generalizedWeakValue}\left(A, B, E, psi, inserted, h\right) = \frac{\operatorname{inner}\left(\mathbb{C}, B\left(A\left(psi\right)\right), E\left(B\left(inserted\right)\right)\right)}{\operatorname{effectWeight}\left(A, B, E, psi\right)})))))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.generalizedWeakValue` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Eq. (2) pairs the final state with the postselection effect. The complex conditional value divides the inserted-state numerator by the nonzero effect weight.

**Definition 1.21 (inputAmplitude).**

$$\forall (k : \mathbb{N}), (\forall (alpha : \mathbb{C}), (\operatorname{inputAmplitude}\left(k, alpha\right) = \operatorname{EuclideanSpace.single}\left(0, alpha\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.inputAmplitude` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Eq. (7) puts alpha in the first input mode and zero in every other mode.

**Definition 1.22 (coherentInput).**

$$\forall (k : \mathbb{N}), (\forall (alpha : \mathbb{C}), (\operatorname{coherentInput}\left(k, alpha\right) = \operatorname{coherent}\left(k + 1, \operatorname{inputAmplitude}\left(k, alpha\right)\right)))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.coherentInput` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The coherent input uses the first input mode.

**Definition 1.23 (singleInput).**

$$\forall (k : \mathbb{N}), (\operatorname{singleInput}\left(k\right) = \operatorname{onePhoton}\left(k + 1, \operatorname{inputAmplitude}\left(k, 1\right)\right))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.singleInput` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The single input has one photon in the first input mode.

**Definition 1.24 (coherentFinal).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\forall (alpha : \mathbb{C}), (\operatorname{coherentFinal}\left(A, B, alpha\right) = \operatorname{gamma}\left(B\right)\left(\operatorname{gamma}\left(A\right)\left(\operatorname{coherentInput}\left(k, alpha\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.coherentFinal` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Definition 1.25 (singleFinal).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\operatorname{singleFinal}\left(A, B\right) = \operatorname{gamma}\left(B\right)\left(\operatorname{gamma}\left(A\right)\left(\operatorname{singleInput}\left(k\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.singleFinal` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Definition 1.26 (coherentProbability).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\forall (alpha : \mathbb{C}), (\forall (m : \mathbb{N}), (\operatorname{coherentProbability}\left(A, B, alpha, m\right) = \operatorname{resolvedProbability}\left(m, \operatorname{coherentFinal}\left(A, B, alpha\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.coherentProbability` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Definition 1.27 (singleProbability).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\forall (m : \operatorname{Fin}\left(2\right)), (\operatorname{singleProbability}\left(A, B, m\right) = \operatorname{resolvedProbability}\left((m : \mathbb{N}), \operatorname{singleFinal}\left(A, B\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.singleProbability` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Definition 1.28 (coherentWeakValue).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\forall (alpha : \mathbb{C}), (\forall (m : \mathbb{N}), (\forall (h : \operatorname{coherentProbability}\left(A, B, alpha, m\right) \ne 0), (\operatorname{coherentWeakValue}\left(A, B, alpha, m, h\right) = \operatorname{generalizedWeakValue}\left(\operatorname{gamma}\left(A\right), \operatorname{gamma}\left(B\right), \operatorname{numberProjector}\left(m\right), \operatorname{coherentInput}\left(k, alpha\right), \operatorname{number}\left(\operatorname{gamma}\left(A\right)\left(\operatorname{coherentInput}\left(k, alpha\right)\right), \operatorname{coherentProbeDomain}\left(A, alpha\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.coherentWeakValue` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Definition 1.29 (singleWeakValue).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (B : \operatorname{Passive}\left(k + 1\right)), (\forall (m : \operatorname{Fin}\left(2\right)), (\forall (h : \operatorname{singleProbability}\left(A, B, m\right) \ne 0), (\operatorname{singleWeakValue}\left(A, B, m, h\right) = \operatorname{generalizedWeakValue}\left(\operatorname{gamma}\left(A\right), \operatorname{gamma}\left(B\right), \operatorname{numberProjector}\left((m : \mathbb{N})\right), \operatorname{singleInput}\left(k\right), \operatorname{number}\left(\operatorname{gamma}\left(A\right)\left(\operatorname{singleInput}\left(k\right)\right), \operatorname{singleProbeDomain}\left(A\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/PassiveFockModel.singleWeakValue` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The same two passive evolutions are used before and after number insertion. Probabilities are real; weak values are complex. Fin 2 is coerced to Nat in the single-photon projector. Membership and nonzero-denominator proof arguments on the right are omitted.

**Theorem 1.30 (headTensor inner).**

$$\forall (H : \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall (u : \operatorname{lp}\left(\operatorname{Function.const}\left(\mathbb{N}, \mathbb{C}\right), 2\right)), (\forall (w : \operatorname{lp}\left(\operatorname{Function.const}\left(\mathbb{N}, \mathbb{C}\right), 2\right)), (\forall (v : H), (\forall (z : H), (\operatorname{inner}\left(\mathbb{C}, \operatorname{headTensor}\left(u, v\right), \operatorname{headTensor}\left(w, z\right)\right) = (\operatorname{inner}\left(\mathbb{C}, u, w\right)) \cdot (\operatorname{inner}\left(\mathbb{C}, v, z\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.headTensor_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The inner product of head tensors is the product of the inner products.

**Theorem 1.31 (single exponentialCoeff inner).**

$$\forall (alpha : \mathbb{C}), (\forall (beta : \mathbb{C}), (\forall (n : \mathbb{N}), (\operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff}\left(alpha, n\right), \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff}\left(beta, n\right)\right) = \frac{((\operatorname{starRingEnd}\left(\mathbb{C}\right)\left(alpha\right)) \cdot (beta))^{n}}{(\operatorname{Nat.factorial}\left(n\right) : \mathbb{C})})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.single_exponentialCoeff_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The coefficient inner product is a term of the complex exponential series.

**Theorem 1.32 (single exponential inner).**

$$\forall (alpha : \mathbb{C}), (\forall (beta : \mathbb{C}), (\operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector}\left(alpha\right), \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector}\left(beta\right)\right) = \operatorname{Complex.exp}\left((\operatorname{starRingEnd}\left(\mathbb{C}\right)\left(alpha\right)) \cdot (beta)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.single_exponential_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The one-mode reproducing kernel is the complex exponential.

**Theorem 1.33 (exponential inner).**

$$\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k\right)), (\forall (gamma : \operatorname{Modes}\left(k\right)), (\operatorname{inner}\left(\mathbb{C}, \operatorname{exponential}\left(k, beta\right), \operatorname{exponential}\left(k, gamma\right)\right) = \operatorname{Complex.exp}\left(\operatorname{inner}\left(\mathbb{C}, beta, gamma\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.exponential_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The reproducing kernel factors over every finite number of modes.

**Theorem 1.34 (exponential total).**

$$\forall (k : \mathbb{N}), (\forall (v : \operatorname{Fock}\left(k\right)), ((\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{inner}\left(\mathbb{C}, v, \operatorname{exponential}\left(k, beta\right)\right) = 0)) \Rightarrow (v = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.exponential_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Orthogonality to every exponential vector forces a vector to vanish. Mode induction reduces the assertion to uniqueness of the coefficients of a complex power series.

**Theorem 1.35 (gamma exponential).**

$$\forall (k : \mathbb{N}), (\forall (V : \operatorname{Passive}\left(k\right)), (\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{gamma}\left(V\right)\left(\operatorname{exponential}\left(k, beta\right)\right) = \operatorname{exponential}\left(k, V\left(beta\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.gamma_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Second quantization acts on exponential vectors by the mode isometry.

**Theorem 1.36 (gamma coherent).**

$$\forall (k : \mathbb{N}), (\forall (V : \operatorname{Passive}\left(k\right)), (\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{gamma}\left(V\right)\left(\operatorname{coherent}\left(k, beta\right)\right) = \operatorname{coherent}\left(k, V\left(beta\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.gamma_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Passive evolution sends a coherent state to the coherent state with transformed amplitude.

**Theorem 1.37 (vacuum exponential inner).**

$$\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{inner}\left(\mathbb{C}, \operatorname{vacuum}\left(k\right), \operatorname{exponential}\left(k, beta\right)\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.vacuum_exponential_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Vacuum pairs to one with every unnormalized exponential vector.

**Theorem 1.38 (onePhoton exponential inner).**

$$\forall (k : \mathbb{N}), (\forall (beta : \operatorname{Modes}\left(k\right)), (\forall (gamma : \operatorname{Modes}\left(k\right)), (\operatorname{inner}\left(\mathbb{C}, \operatorname{onePhoton}\left(k, beta\right), \operatorname{exponential}\left(k, gamma\right)\right) = \operatorname{inner}\left(\mathbb{C}, beta, gamma\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.onePhoton_exponential_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The one-photon sector pairs with an exponential vector by the mode-space inner product.

**Theorem 1.39 (gamma onePhoton).**

$$\forall (k : \mathbb{N}), (\forall (V : \operatorname{Passive}\left(k\right)), (\forall (beta : \operatorname{Modes}\left(k\right)), (\operatorname{gamma}\left(V\right)\left(\operatorname{onePhoton}\left(k, beta\right)\right) = \operatorname{onePhoton}\left(k, V\left(beta\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.gamma_onePhoton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The one-photon embedding intertwines passive evolution and second quantization.

**Theorem 1.40 (projector weight).**

$$\forall (k : \mathbb{N}), (\forall (m : \mathbb{N}), (\forall (psi : \operatorname{Fock}\left(k + 1\right)), (\operatorname{inner}\left(\mathbb{C}, psi, \operatorname{numberProjector}\left(m\right)\left(psi\right)\right) = (\operatorname{resolvedProbability}\left(m, psi\right) : \mathbb{C}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.projector_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

The projector effect weight is the real resolved probability, coerced to the complex field.

**Theorem 1.41 (coherentProbeDomain).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\forall (alpha : \mathbb{C}), (\operatorname{NumberDomain}\left(\operatorname{gamma}\left(A\right)\left(\operatorname{coherentInput}\left(k, alpha\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.coherentProbeDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Every coherently prepared probe vector lies in the number-operator domain.

**Theorem 1.42 (singleProbeDomain).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{Passive}\left(k + 1\right)), (\operatorname{NumberDomain}\left(\operatorname{gamma}\left(A\right)\left(\operatorname{singleInput}\left(k\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PassiveFockModel.singleProbeDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Every single-photon probe vector lies in the number-operator domain.

## References

- Truth anchor: `D5/S3/Quantum/PassiveFockModel.Fock`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.Hilbert`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.Modes`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.NumberDomain`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.Passive`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherent`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherentFinal`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherentInput`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherentProbability`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherentProbeDomain`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.coherentWeakValue`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.effectWeight`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.exponential`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.exponential_inner`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.exponential_total`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.fockHilbert`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.gamma`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.gamma_coherent`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.gamma_exponential`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.gamma_onePhoton`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.generalizedWeakValue`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.headTensor`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.headTensor_inner`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.hilbertStep`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.inputAmplitude`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.number`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.numberExponential`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.numberProjector`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.onePhoton`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.onePhoton_exponential_inner`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.projector_weight`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.resolvedProbability`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.singleFinal`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.singleInput`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.singleProbability`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.singleProbeDomain`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.singleWeakValue`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.single_exponentialCoeff_inner`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.single_exponential_inner`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.tail`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.vacuum`
- Truth anchor: `D5/S3/Quantum/PassiveFockModel.vacuum_exponential_inner`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter](QuantumChannels/FockAttenuator/BeamSplitter.md)
