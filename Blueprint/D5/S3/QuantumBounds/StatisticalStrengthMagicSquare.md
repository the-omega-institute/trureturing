# Statistical strength of the two-singlet magic square

## Abstract

Four joint settings on two literal singlets beat twice CHSH under all three statistical-strength conventions.

**Definition 1.1 (Uniform finite distributions).**

$$\forall n \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)] \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{uniform}\left(n\right)\left(i\right) = (n:\operatorname{NNReal})^{-1}$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.uniform` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section IV.B, p. 8: “where σ° denotes the uniform distribution over the settings.” The existing Mathlib type stdSimplex NNReal (Fin n) consists of nonnegative masses summing to one. Fin n indexes n points by 0,…,n−1; [NeZero n] excludes an empty uniform law. Application uses the existing FunLike coercion of stdSimplex.

**Definition 1.2 (Finite relative entropy in bits).**

$$\forall alpha \in Type,\; [\operatorname{Fintype}\left(alpha\right)] \forall q \in alpha \to \operatorname{NNReal},\; \forall p \in alpha \to \operatorname{NNReal},\; \operatorname{D}\left(q, p\right) = \operatorname{ite}\left(\forall z \in alpha,\; (p\left(z\right) = 0) \Rightarrow (q\left(z\right) = 0), (\sum_{z:alpha} (\frac{(q\left(z\right):\mathbb{R}) \cdot \operatorname{Real}.\operatorname{log}\left(\frac{(q\left(z\right):\mathbb{R})}{(p\left(z\right):\mathbb{R})}\right)}{\operatorname{Real}.\operatorname{log}\left(2\right)}):\operatorname{EReal}), \operatorname{Top}.\operatorname{top}\left(\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.D` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section IV.A, p. 6: “For two (arbitrary) distributions Q and P defined over Z, the Kullback-Leibler (KL) divergence from Q to P is defined as” D(Q∥P) := ∑z∈Z Q(z) log(Q(z)/P(z)), “where the logarithm is taken here, as in the rest of the paper, to base 2.” The zero-mass conventions make a zero q mass contribute zero and a positive q mass above zero p mass contribute infinity. Real.log is the natural logarithm, so division by Real.log 2 converts to bits. The finite branch is coerced from R to EReal; ⊤ is EReal's positive infinity. The displayed expression uses Lean's total real division and logarithm, including log 0 = 0, only inside the absolutely continuous branch.

**Definition 1.3 (All local response mixtures).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; \forall mu \in \operatorname{stdSimplex}\left(\operatorname{NNReal}, (\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right)) \times (\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right))\right),\; \forall x \in \operatorname{Fin}\left(s\right),\; \forall y \in \operatorname{Fin}\left(s\right),\; \forall a \in \operatorname{Fin}\left(o\right),\; \forall b \in \operatorname{Fin}\left(o\right),\; \operatorname{localBehavior}\left(mu\right)\left(x, y, a, b\right) = \sum_{t:(\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right)) \times (\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right))} (\operatorname{ite}\left((t.1\left(x\right) = a) \land (t.2\left(y\right) = b), mu\left(t\right), 0\right))$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.localBehavior` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section II.D, p. 5: “A local theory π may be viewed as a probability distribution for (X₁,X₂,Y₁,Y₂).” For s settings and o outcomes, the literal generalization is: μ is any normalized distribution on pairs of deterministic response functions Fin s → Fin o. The finite sum marginalizes the responses at x and y. It includes every local theory, including nonrational weights; the proof never limits μ to a list of strategies.

**Definition 1.4 (Independent setting laws).**

$$\forall s \in \mathbb{N},\; \forall alpha \in \operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right)\right),\; \forall beta \in \operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right)\right),\; \forall z \in \operatorname{Fin}\left(s\right) \times \operatorname{Fin}\left(s\right),\; \operatorname{productLaw}\left(alpha, beta\right)\left(z\right) = alpha\left(z.1\right) \cdot beta\left(z.2\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.productLaw` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section IV.B, p. 8 requires that “the distribution for each party is uncorrelated with the distributions of the other parties”. Two marginal distributions alpha and beta yield their pointwise product on pairs of settings. The stdSimplex proofs verify its normalization.

**Definition 1.5 (Uniform pairs of settings).**

$$\forall s \in \mathbb{N},\; [\operatorname{NeZero}\left(s\right)] \operatorname{uniformLaw}\left(s\right) = \operatorname{productLaw}\left(\operatorname{uniform}\left(s\right), \operatorname{uniform}\left(s\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.uniformLaw` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

This is the source's σ°: the product of the two uniform setting laws, with s² equally weighted pairs.

**Definition 1.6 (Settings and outcomes in one distribution).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; \forall sigma \in \operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right) \times \operatorname{Fin}\left(s\right)\right),\; \forall q \in \operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(o\right) \to \left(\operatorname{Fin}\left(o\right) \to \operatorname{NNReal}\right)\right)\right),\; \forall z \in (\operatorname{Fin}\left(s\right) \times \operatorname{Fin}\left(s\right)) \times (\operatorname{Fin}\left(o\right) \times \operatorname{Fin}\left(o\right)),\; \operatorname{joint}\left(sigma, q\right)\left(z\right) = sigma\left(z.1\right) \cdot q\left(z.1.1, z.1.2, z.2.1, z.2.2\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.joint` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section II.B, p. 5: “According to QM, the total outcome (X,Y,A,B) of a single trial is then distributed as Qσ, defined by” Qσ(X = x,Y = y,A = a,B = b) := σab Qab(X = x,Y = y). The index z groups the setting pair z.1 and the outcome pair z.2. Its four entries are selected using Lean's product projections. q is the conditional outcome law; sigma is a distribution of settings.

**Definition 1.7 (Infimum over every local theory).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(o\right) \to \left(\operatorname{Fin}\left(o\right) \to \operatorname{NNReal}\right)\right)\right),\; \forall sigma \in \operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right) \times \operatorname{Fin}\left(s\right)\right),\; \operatorname{strengthAt}\left(q, sigma\right) = \operatorname{iInf}_{mu:\operatorname{stdSimplex}\left(\operatorname{NNReal}, (\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right)) \times (\operatorname{Fin}\left(s\right) \to \operatorname{Fin}\left(o\right))\right)} (\operatorname{D}\left(\operatorname{joint}\left(sigma, q\right), \operatorname{joint}\left(sigma, \operatorname{localBehavior}\left(mu\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.strengthAt` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Section IV.B, p. 8 defines D(Qσ∥Pσ) as the infimum of D(Qσ∥Pσ,π) over π∈Π. Here iInf is the infimum in EReal, over the entire stdSimplex of deterministic-response mixtures.

**Definition 1.8 (Strength for uniform settings).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; [\operatorname{NeZero}\left(s\right)] \forall q \in \operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(o\right) \to \left(\operatorname{Fin}\left(o\right) \to \operatorname{NNReal}\right)\right)\right),\; \operatorname{S}_{uni}\left(q\right) = \operatorname{strengthAt}\left(q, \operatorname{uniformLaw}\left(s\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S_uni` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Definition 1, Section IV.B, p. 8: “When each measurement setting is sampled with equal probability, the resulting strength S_Q^UNI is defined by” S_Q^UNI := D(Qσ°∥Pσ°) = infπ∈Π D(Qσ°∥Pσ°,π), “where σ° denotes the uniform distribution over the settings.” The source symbol S_Q^UNI is encoded by S_uni q; strengthAt supplies the infimum.

**Definition 1.9 (Strength for uncorrelated settings).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(o\right) \to \left(\operatorname{Fin}\left(o\right) \to \operatorname{NNReal}\right)\right)\right),\; \operatorname{S}\left(q\right) = \operatorname{iSup}_{alpha:\operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right)\right)} (\operatorname{iSup}_{beta:\operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right)\right)} (\operatorname{strengthAt}\left(q, \operatorname{productLaw}\left(alpha, beta\right)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Definition 2, Section IV.B, p. 8: “When the experimenter QM is allowed to choose any distribution on measurement settings, as long as the distribution for each party is uncorrelated with the distributions of the other parties, the resulting strength S_Q^UC is defined by” S_Q^UC := supσ∈ΣUC D(Qσ∥Pσ) = supσ∈ΣUC infπ∈Π D(Qσ∥Pσ,π), “where σ∈ΣUC denotes the use of uncorrelated settings.” S q is literally the supremum over pairs of marginal distributions, each giving productLaw alpha beta.

**Definition 1.10 (Strength for correlated settings).**

$$\forall s \in \mathbb{N},\; \forall o \in \mathbb{N},\; \forall q \in \operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(s\right) \to \left(\operatorname{Fin}\left(o\right) \to \left(\operatorname{Fin}\left(o\right) \to \operatorname{NNReal}\right)\right)\right),\; \operatorname{S}_{cor}\left(q\right) = \operatorname{iSup}_{sigma:\operatorname{stdSimplex}\left(\operatorname{NNReal}, \operatorname{Fin}\left(s\right) \times \operatorname{Fin}\left(s\right)\right)} (\operatorname{strengthAt}\left(q, sigma\right))$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S_cor` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Definition 3, Section IV.B, p. 8: “When the experimeniter QM is allowed to choose any distribution on measurement settings (including correlated distributions), the resulting strength S_Q^COR is defined by” S_Q^COR := supσ∈Σ D(Qσ∥Pσ) = supσ∈Σ infπ∈Π D(Qσ∥Pσ,π), “where σ∈Σ denoted the use of correlated settings.” The words “experimeniter” and “denoted” reproduce the source. S_cor q takes the supremum over all normalized setting laws.

**Definition 1.11 (The literal Bell singlet).**

$$\forall a \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{singletCoefficient}\left(a, b\right) = \operatorname{ite}\left((a = 0) \land (b = 1), (\operatorname{Real}.\operatorname{sqrt}\left(2\right):\mathbb{C})^{-1}, \operatorname{ite}\left((a = 1) \land (b = 0), -(\operatorname{Real}.\operatorname{sqrt}\left(2\right):\mathbb{C})^{-1}, 0\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.singletCoefficient` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The two-qubit singlet is (|01⟩−|10⟩)/sqrt 2. These are its literal complex amplitudes in the computational basis. The minus sign distinguishes the singlet from Phi-plus. The inverse square root is in C.

**Definition 1.12 (Two singlets shared between the parties).**

$$\forall z \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{twoSinglets}\left(z\right) = \operatorname{singletCoefficient}\left(z.1.1, z.2.1\right) \cdot \operatorname{singletCoefficient}\left(z.1.2, z.2.2\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.twoSinglets` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The global index z consists of Alice's two-qubit basis index z.1 and Bob's z.2. Multiplying singletCoefficient on each corresponding Alice–Bob pair is the literal tensor product of two singlets, regrouped by party. No entanglement proxy replaces that state.

**Definition 1.13 (Four nonzero orthogonal projectors).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall P \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{IsPVM}\left(P\right) = \left((\forall a \in \operatorname{Fin}\left(4\right),\; (P\left(a\right) \ne 0) \land ((\operatorname{star}\left(P\left(a\right)\right) = P\left(a\right)) \land (P\left(a\right) \cdot P\left(a\right) = P\left(a\right)))) \land ((\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; (a \ne b) \Rightarrow (P\left(a\right) \cdot P\left(b\right) = 0)) \land (\sum_{a:\operatorname{Fin}\left(4\right)} (P\left(a\right)) = 1))\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.IsPVM` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Under the four-nonzero-outcome measurement convention, each setting has four nonzero projectors. Each projector is self-adjoint and idempotent; distinct outcomes are orthogonal; their sum is the identity. star on matrices is conjugate transpose. The anonymous Fintype and DecidableEq brackets are Lean instance arguments, not new mathematical variables.

**Definition 1.14 (Two parties, four settings, four outcomes).**

$$\begin{aligned}\operatorname{Experiment}:Type\\\forall e \in \operatorname{Experiment},\; \operatorname{Experiment}.\operatorname{alice}\left(e\right):\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)\right)\\\forall e \in \operatorname{Experiment},\; \operatorname{Experiment}.\operatorname{bob}\left(e\right):\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.Experiment` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The structure has exactly the fields alice and bob, both with type Fin 4 → Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) C. The first argument indexes a local setting and the second an outcome. Each party's operator acts jointly on its two qubits. Together with Valid, this is the source's 2×4×4 experiment type.

**Definition 1.15 (Validity of all eight settings).**

$$\forall e \in \operatorname{Experiment},\; \operatorname{Valid}\left(e\right) = \left((\forall x \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPVM}\left(\operatorname{Experiment}.\operatorname{alice}\left(e, x\right)\right)) \land (\forall y \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPVM}\left(\operatorname{Experiment}.\operatorname{bob}\left(e, y\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.Valid` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Every Alice setting and every Bob setting satisfies IsPVM. In particular the four outcomes of every setting are nonzero.

**Definition 1.16 (Products of single-qubit operators).**

$$\forall P \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{ProductOperator}\left(P\right) = \left(\exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \exists B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; P = \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (u v:\mathbb{C}), u \cdot v), A, B\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.ProductOperator` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

A product operator is literally a Kronecker product A ⊗ₖ B of arbitrary two-by-two complex matrices. No rank or separability surrogate replaces that existential definition.

**Definition 1.17 (A joint measurement on a pair).**

$$\forall e \in \operatorname{Experiment},\; \operatorname{JointMeasurement}\left(e\right) = \left((\exists x \in \operatorname{Fin}\left(4\right),\; \exists a \in \operatorname{Fin}\left(4\right),\; \neg \operatorname{ProductOperator}\left(\operatorname{Experiment}.\operatorname{alice}\left(e, x, a\right)\right)) \lor (\exists y \in \operatorname{Fin}\left(4\right),\; \exists b \in \operatorname{Fin}\left(4\right),\; \neg \operatorname{ProductOperator}\left(\operatorname{Experiment}.\operatorname{bob}\left(e, y, b\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.JointMeasurement` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Conjecture 5, Section VI.D, p. 11 requires “involving joint measurements on the pairs.” This means that at least one local projector, for Alice or Bob, is not a product of single-qubit operators. The existential quantifiers range over actual settings and outcomes.

**Definition 1.18 (Born amplitudes of the two-singlet experiment).**

$$\forall e \in \operatorname{Experiment},\; \forall x \in \operatorname{Fin}\left(4\right),\; \forall y \in \operatorname{Fin}\left(4\right),\; \forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{born}\left(e, x, y, a, b\right) = \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{twoSinglets}\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (u v:\mathbb{C}), u \cdot v), \operatorname{Experiment}.\operatorname{alice}\left(e, x, a\right), \operatorname{Experiment}.\operatorname{bob}\left(e, y, b\right)\right), \operatorname{twoSinglets}\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.born` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The expression is the literal Born expectation: dotProduct of star twoSinglets with the action of the Kronecker product of the two local outcome projectors. All four indices range over Fin 4.

**Definition 1.19 (Conditional quantum probabilities).**

$$\forall e \in \operatorname{Experiment},\; \forall x \in \operatorname{Fin}\left(4\right),\; \forall y \in \operatorname{Fin}\left(4\right),\; \forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{quantum}\left(e\right)\left(x, y, a, b\right) = \operatorname{Real}.\operatorname{toNNReal}\left(\operatorname{Complex}.\operatorname{re}\left(\operatorname{born}\left(e, x, y, a, b\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.quantum` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The quantum conditional law is Real.toNNReal of the real part of the Born expectation. Validity proves that this real part is nonnegative and that the probabilities sum to one; the truncation thus leaves every valid Born probability unchanged.

**Definition 1.20 (Alice's CHSH projectors).**

$$\forall x \in \operatorname{Fin}\left(2\right),\; \forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{chshAlice}\left(x, a\right) = \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1}{2}:\mathbb{C}), 1 + \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{ite}\left(a = 0, 1, -1\right), \operatorname{ite}\left(x = 0, \operatorname{qubitZ}, \operatorname{qubitX}\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshAlice` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Appendix III.C, pp. 18–20 gives the CHSH quantum table. These two-outcome projectors use frozen qubitZ and qubitX. Settings and outcomes have indices 0 and 1. The sign is +1 for outcome 0 and −1 for outcome 1.

**Definition 1.21 (Bob's singlet-conjugated CHSH projectors).**

$$\forall y \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{chshBob}\left(y, b\right) = \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1}{2}:\mathbb{C}), 1 + \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{ite}\left(b = 0, 1, -1\right), \operatorname{HSMul}.\operatorname{hSMul}\left(-(\operatorname{Real}.\operatorname{sqrt}\left(2\right):\mathbb{C})^{-1}, \operatorname{ite}\left(y = 0, \operatorname{qubitZ} + \operatorname{qubitX}, \operatorname{qubitZ} - \operatorname{qubitX}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshBob` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The source realizes its CHSH table with Phi-plus. Bob's observables are conjugated by the local singlet unitary. On a literal singlet they are −(Z+X)/sqrt 2 and −(Z−X)/sqrt 2; these projectors reproduce the source table, with probabilities (2+sqrt 2)/8 for a winning output and (2−sqrt 2)/8 otherwise.

**Definition 1.22 (The CHSH Born expectation on a singlet).**

$$\forall x \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \forall a \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{chshBorn}\left(x, y, a, b\right) = \operatorname{dotProduct}\left(\operatorname{star}\left((\lambda (z:\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \operatorname{singletCoefficient}\left(z.1, z.2\right))\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda (u v:\mathbb{C}), u \cdot v), \operatorname{chshAlice}\left(x, a\right), \operatorname{chshBob}\left(y, b\right)\right), (\lambda (z:\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \operatorname{singletCoefficient}\left(z.1, z.2\right))\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshBorn` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The vector in both dotProduct and mulVec has entries singletCoefficient z.1 z.2. This expectation uses a literal singlet and the displayed CHSH PVMs, not the source's Phi-plus state.

**Definition 1.23 (The physical CHSH conditional law).**

$$\forall x \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \forall a \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{chsh}\left(x, y, a, b\right) = \operatorname{Real}.\operatorname{toNNReal}\left(\operatorname{Complex}.\operatorname{re}\left(\operatorname{chshBorn}\left(x, y, a, b\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chsh` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The probabilities are Real.toNNReal of the real parts of the literal singlet Born expectations. The private source_chsh_born calculation connects this law to Appendix III.C's table and is used in the arbitrary-setting-law upper bound.

**Definition 1.24 (Conjecture 5).**

$$\exists e \in \operatorname{Experiment},\; (\operatorname{Valid}\left(e\right)) \land ((\operatorname{JointMeasurement}\left(e\right)) \land (\operatorname{S}_{uni}\left(\operatorname{quantum}\left(e\right)\right) > 2 \cdot \operatorname{S}_{cor}\left(\operatorname{chsh}\right)))$$

*Formalization.* `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.claim` (`✓ std3`).

*Citation.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

Conjecture 5, Section VI.D, p. 11: “There is an experiment on pairs of Bell singlets, of the 2×4×4 type, more than twice as strong as CHSH, and involving joint measurements on the pairs.” The encoding is: there exists e : Experiment with Valid e and JointMeasurement e, and S_uni (quantum e) > 2 * S_cor chsh. Since the uniform strength is no larger than the product-setting strength, which is no larger than the correlated-setting strength, this inequality implies the required comparison in each of the source's three senses.

**Theorem 1.25 (The two-singlet experiment proves the conjecture).**

$$\exists e \in \operatorname{Experiment},\; (\operatorname{Valid}\left(e\right)) \land ((\operatorname{JointMeasurement}\left(e\right)) \land (\operatorname{S}_{uni}\left(\operatorname{quantum}\left(e\right)\right) > 2 \cdot \operatorname{S}_{cor}\left(\operatorname{chsh}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result` (`✓ std3`). ∎

*Resolves.* `Problems/van-dam-gill-grunwald-2005-two-singlet-strength` (proved) by `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"van-dam-gill-grunwald-2005-two-singlet-strength","declaration_gid":"D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* W. van Dam; R. D. Gill; P. D. Grünwald (2005). *The Statistical Strength of Nonlocality Proofs*. DOI: [10.1109/TIT.2005.851738](https://doi.org/10.1109/TIT.2005.851738). URL: <https://arxiv.org/abs/quant-ph/0307125v2>.

*Commentary.*

The commuting magic-square rows and columns give four nonzero-outcome PVMs on each side. Bob's transpose and local singlet conjugation give the Born trace identity, and losing parity outcomes have zero probability. Every pair of deterministic local response functions wins at most eight of the nine magic-square contexts. Averaging preserves that bound for every normalized local mixture. Coarse-graining the uniform joint law into outside, winning and losing bins and applying the frozen log-sum inequality proves S_uni ≥ (9/16) log(9/8)/log 2. A single local CHSH reference mixture gives S_cor CHSH ≤ c for every setting law. The fulfilled rational logarithm enclosures prove 2c < 93/1000 < 95/1000 < (9/16) log(9/8)/log 2. A nonzero product-operator minor proves that an Alice projector is joint. No exact optimal strength or global optimality claim is made.

## References

- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.D`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.Experiment`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.IsPVM`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.JointMeasurement`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.ProductOperator`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S_cor`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.S_uni`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.Valid`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.born`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chsh`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshAlice`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshBob`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.chshBorn`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.claim`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.joint`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.localBehavior`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.productLaw`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.quantum`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.singletCoefficient`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.strengthAt`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.twoSinglets`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.uniform`
- Truth anchor: `D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.uniformLaw`
- Dependency: [D5/S3/DivergenceSupport/LogSumInequality](../DivergenceSupport/LogSumInequality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Entropy/Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Quantum/Information/StabilizerPairLocalUnitaryInequivalence.md)
