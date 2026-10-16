# Unitary entanglement assistance under a vacuum energy restriction

## Abstract

Four unitary encodings of a partially entangled state outperform every unassisted strategy at the same energy.

Alice receives an input x, applies a unitary to her part of a shared pure state, and sends that part to Bob. Bob chooses a setting y and measures the joint system, obtaining an outcome b. This is the unitary case of the entanglement-assisted prepare-and-measure model in Section II, Eqs. (1)–(2), and Section IV.A. All sums range over the entire indicated finite type. Matrix entries are complex, probabilities and task values are real, and brackets denote anonymous typeclass assumptions.

**Definition 1.1 (Finite positive operator-valued measurements).**

$$\forall n \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(n\right)], [\operatorname{\mathit{DecidableEq}}\left(n\right)], [\operatorname{\mathit{Fintype}}\left(B\right)], \forall M \in B \to \operatorname{\mathit{Matrix}}\left(n, n, \mathit{Complex}\right),\; (\operatorname{\mathit{IsPOVM}}\left(M\right)) \Leftrightarrow ((\forall b \in B,\; \operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(M\left(b\right)\right)) \land (\sum_{b:B}(M\left(b\right)) = 1))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.IsPOVM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Every effect is positive semidefinite and the effects sum to the identity. The carrier n and outcome type B are finite; n also has decidable equality.

**Definition 1.2 (A pure state with local unitary encodings).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(B\right)], \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall M \in Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right)\right),\; (\operatorname{\mathit{UnitaryStrategy}}\left(\mathit{Psi}, U, M\right)) \Leftrightarrow ((\sum_{i:\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right)}(\operatorname{\mathit{Complex}}.\operatorname{\mathit{normSq}}\left(\mathit{Psi}\left(i\right)\right)) = 1) \land (\forall y \in Y,\; \operatorname{\mathit{IsPOVM}}\left(M\left(y\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.UnitaryStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The squared moduli of the state coordinates sum to one. The type of U requires a unitary matrix on Alice's factor for every input. For every setting, Bob's effects form a POVM on the product of the two factors. These are the pure-state unitary strategies considered in Section IV.A.

**Definition 1.3 (The state after the message is encoded).**

$$\forall X \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall x \in X,\; \operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{kronecker}}\left((U\left(x\right):\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right)), (1:\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dB}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right), \mathit{Complex}\right))\right), \mathit{Psi}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.encoded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Alice acts on her factor with U(x), while the identity acts on Bob's factor. The Kronecker product followed by matrix-vector multiplication gives the joint state received by Bob, specializing Eq. (1) to a unitary operation.

**Definition 1.4 (The outcome probability of the joint measurement).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall M \in Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right)\right),\; \forall b \in B,\; \forall x \in X,\; \forall y \in Y,\; \operatorname{\mathit{unitaryProb}}\left(\mathit{Psi}, U, M, b, x, y\right) = \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(M\left(y, b\right), \operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryProb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The real part of the quadratic form of M(y,b) on the encoded vector is the Born probability in Eq. (2). The conjugation in star is coordinatewise, and dotProduct sums products of matching coordinates. The expression is defined for arbitrary vectors and effects; UnitaryStrategy supplies their physical normalization.

**Definition 1.5 (The vacuum component of the transmitted subsystem).**

$$\forall X \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; [\operatorname{\mathit{NeZero}}\left(\mathit{dA}\right)], \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall x \in X,\; \operatorname{\mathit{unitaryVacuum}}\left(\mathit{Psi}, U, x\right) = \sum_{j:\operatorname{\mathit{Fin}}\left(\mathit{dB}\right)}((\Vert\operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{mk}}\left(0, j\right)\right)\Vert)^{2})$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Sum the squared moduli of the encoded coordinates whose Alice index is zero. This is the vacuum population of the reduced message state. Equation (3) requires this quantity to be at least 1 − omega for every input, where omega is the allowed energy and NeZero dA makes the vacuum index available.

**Definition 1.6 (Unassisted quantum communication with shared randomness).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall L \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(B\right)], [\operatorname{\mathit{Fintype}}\left(L\right)], \forall d \in \mathit{Nat},\; \forall q \in L \to \mathit{Real},\; \forall rho \in L \to \left(X \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right),\; \forall M \in L \to \left(Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right)\right),\; (\operatorname{\mathit{QCStrategy}}\left(q, \mathit{rho}, M\right)) \Leftrightarrow ((\forall l \in L,\; 0 \le q\left(l\right)) \land ((\sum_{l:L}(q\left(l\right)) = 1) \land ((\forall l \in L,\; \forall x \in X,\; (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(\mathit{rho}\left(l, x\right)\right)) \land (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left(\mathit{rho}\left(l, x\right)\right) = 1)) \land (\forall l \in L,\; \forall y \in Y,\; (\forall b \in B,\; \operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(M\left(l, y, b\right)\right)) \land (\sum_{b:B}(M\left(l, y, b\right)) = 1)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.QCStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The finite random variable l has nonnegative weights q summing to one. Conditional on l and x, Alice sends a positive semidefinite trace-one matrix rho(l,x). Conditional on l and y, Bob measures a POVM. These are the states and measurements of the unassisted quantum model in Section II.B and Eq. (4). No entangled system is retained by Bob.

**Definition 1.7 (Probabilities averaged over the shared random variable).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall L \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(L\right)], \forall d \in \mathit{Nat},\; \forall q \in L \to \mathit{Real},\; \forall rho \in L \to \left(X \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right),\; \forall M \in L \to \left(Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right)\right),\; \forall b \in B,\; \forall x \in X,\; \forall y \in Y,\; \operatorname{\mathit{qcProb}}\left(q, \mathit{rho}, M, b, x, y\right) = \sum_{l:L}((q\left(l\right)) \cdot (\operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left((\mathit{rho}\left(l, x\right)) \cdot (M\left(l, y, b\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcProb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Equation (4) averages the conditional Born probabilities with the weights q. The real part of the trace is explicit. The definition itself places no positivity or normalization conditions on the weights, states or effects.

**Definition 1.8 (The averaged vacuum population).**

$$\forall X \in \mathit{Type},\; \forall L \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(L\right)], \forall d \in \mathit{Nat},\; [\operatorname{\mathit{NeZero}}\left(d\right)], \forall q \in L \to \mathit{Real},\; \forall rho \in L \to \left(X \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right),\; \forall x \in X,\; \operatorname{\mathit{qcVacuum}}\left(q, \mathit{rho}, x\right) = \sum_{l:L}((q\left(l\right)) \cdot (\operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\mathit{rho}\left(l, x, 0, 0\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Equation (5) averages the vacuum entries of the conditional message states. The energy restriction is qcVacuum(q,rho,x) at least 1 − omega for each x. It constrains the average over l and permits the conditional energies to differ.

**Definition 1.9 (A general finite linear communication task).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(X\right)], [\operatorname{\mathit{Fintype}}\left(Y\right)], [\operatorname{\mathit{Fintype}}\left(B\right)], \forall c \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \forall p \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \operatorname{\mathit{taskValue}}\left(c, p\right) = \sum_{b:B}(\sum_{x:X}(\sum_{y:Y}((c\left(b, x, y\right)) \cdot (p\left(b, x, y\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.taskValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Each real coefficient c(b,x,y) multiplies the corresponding probability, and the sum includes all outcomes, inputs and settings. The coefficients are arbitrary; this includes success probabilities as well as other linear figures of merit.

**Definition 1.10 (The positive answer to the question for general tasks).**

$$(\mathit{claim}) \Leftrightarrow (\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(X\right)], [\operatorname{\mathit{Fintype}}\left(Y\right)], [\operatorname{\mathit{Fintype}}\left(B\right)], \forall c \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \forall omega \in \mathit{Real},\; (0 \le \mathit{omega}) \Rightarrow ((\mathit{omega} < \frac{1}{2}) \Rightarrow (\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; [\operatorname{\mathit{NeZero}}\left(\mathit{dA}\right)], \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall M \in Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right)\right),\; (\operatorname{\mathit{UnitaryStrategy}}\left(\mathit{Psi}, U, M\right)) \Rightarrow ((\forall x \in X,\; 1 - \mathit{omega} \le \operatorname{\mathit{unitaryVacuum}}\left(\mathit{Psi}, U, x\right)) \Rightarrow (\exists d \in \mathit{Nat},\; \exists [\operatorname{\mathit{NeZero}}\left(d\right)], \exists L \in \mathit{Type},\; \exists [\operatorname{\mathit{Fintype}}\left(L\right)], \exists q \in L \to \mathit{Real},\; \exists rho \in L \to \left(X \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right),\; \exists N \in L \to \left(Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(d\right), \operatorname{\mathit{Fin}}\left(d\right), \mathit{Complex}\right)\right)\right),\; (\operatorname{\mathit{QCStrategy}}\left(q, \mathit{rho}, N\right)) \land ((\forall x \in X,\; 1 - \mathit{omega} \le \operatorname{\mathit{qcVacuum}}\left(q, \mathit{rho}, x\right)) \land (\operatorname{\mathit{taskValue}}\left(c, \operatorname{\mathit{unitaryProb}}\left(\mathit{Psi}, U, M\right)\right) \le \operatorname{\mathit{taskValue}}\left(c, \operatorname{\mathit{qcProb}}\left(q, \mathit{rho}, N\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Section VI asks whether unitary encoding remains resourceless for general tasks. The displayed proposition is the positive answer for finite alphabets and 0 ≤ omega < 1/2: every unitary entanglement-assisted value would be matched or exceeded by an unassisted strategy with the same energy bound. The latter may use any positive finite message dimension and any finite shared random variable. Result 4 concerns only probabilistic transmission of a bit; the proposition here quantifies over all finite linear tasks.

**Theorem 1.11 (Four messages give a strict advantage below half-unit energy).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/roch-i-carceller-tavakoli-2025-energy-restricted-unitary-encoding` (refuted) by `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"roch-i-carceller-tavakoli-2025-energy-restricted-unitary-encoding","declaration_gid":"D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Take inputs and outcomes (u,v) in Fin 2 × Fin 2, one measurement setting, and task weights c(b,x,y) = 1/4 when b = x and zero otherwise. Alice and Bob share the pure state (4/5)|00⟩ + (3/5)|11⟩. Set Z = [[1,0],[0,−1]] and R = [[4/5,−3/5],[3/5,4/5]]. For input (u,v), Alice applies Z^u R Z^v. Bob measures the four rank-one projectors onto the orthonormal vectors m_(u,v) = (1/2)(1,−(−1)^v,(−1)^u,(−1)^(u+v)), in the coordinate order (00,01,10,11).

For input (u,v), the encoded vector has coordinates (16/25,−(9/25)(−1)^v,(12/25)(−1)^u,(12/25)(−1)^(u+v)). Its vacuum component is 337/625 for every input. Thus the energy restriction holds with omega = 288/625 < 1/2. The overlap with the corresponding measurement vector is 49/50, giving task value 2401/2500.

For every density matrix rho and effect 0 ≤ E ≤ I, Re Tr(E rho) − Re E_(0,0) ≤ sqrt(1 − Re rho_(0,0)). For a pure state, compression to the span of its vacuum and nonvacuum parts reduces this inequality to a two-dimensional Hermitian involution. Spectral decomposition and concavity of the square root give the density-matrix case. Summing the effect inequality over the four guesses and averaging over the shared random variable bounds every unassisted value for this task by 1/4 + sqrt(omega) under the same averaged energy restriction. Since sqrt(288/625) < 17/25, every such value is less than 93/100, whereas 2401/2500 > 93/100. Hence claim is false.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.IsPOVM`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.QCStrategy`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.UnitaryStrategy`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.encoded`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcProb`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcVacuum`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.taskValue`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryProb`
- Truth anchor: `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryVacuum`
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
