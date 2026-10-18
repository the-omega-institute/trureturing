# Unitary entanglement assistance under a vacuum energy restriction

## Abstract

Four unitary encodings of a partially entangled state outperform every unassisted strategy at the same energy.

Alice receives an input x, applies a unitary to her part of a shared pure state, and sends that part to Bob. Bob chooses a setting y and measures the joint system, obtaining an outcome b. This is the unitary case of the entanglement-assisted prepare-and-measure model in Section II, Eqs. (1)–(2), and Section IV.A. All finite sums range over the entire indicated finite type; each tsum ranges over its indicated arbitrary index type. Matrix entries are complex, probabilities and task values are real, and brackets denote anonymous typeclass assumptions.

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

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The squared moduli of the state coordinates sum to one. The type of U requires a unitary matrix on Alice's factor for every input. For every setting, Bob's effects form a POVM on the product of the two factors. These are the pure-state unitary strategies considered in Section IV.A.

**Definition 1.3 (The state after the message is encoded).**

$$\forall X \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall x \in X,\; \operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{kronecker}}\left((U\left(x\right):\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right)), (1:\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dB}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right), \mathit{Complex}\right))\right), \mathit{Psi}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.encoded` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Alice acts on her factor with U(x), while the identity acts on Bob's factor. The Kronecker product followed by matrix-vector multiplication gives the joint state received by Bob, specializing Eq. (1) to a unitary operation.

**Definition 1.4 (The outcome probability of the joint measurement).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall M \in Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right)\right),\; \forall b \in B,\; \forall x \in X,\; \forall y \in Y,\; \operatorname{\mathit{unitaryProb}}\left(\mathit{Psi}, U, M, b, x, y\right) = \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(M\left(y, b\right), \operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryProb` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The real part of the quadratic form of M(y,b) on the encoded vector is the Born probability in Eq. (2). The conjugation in star is coordinatewise, and dotProduct sums products of matching coordinates. The expression is defined for arbitrary vectors and effects; UnitaryStrategy supplies their physical normalization.

**Definition 1.5 (The vacuum component of the transmitted subsystem).**

$$\forall X \in \mathit{Type},\; \forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; [\operatorname{\mathit{NeZero}}\left(\mathit{dA}\right)], \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall x \in X,\; \operatorname{\mathit{unitaryVacuum}}\left(\mathit{Psi}, U, x\right) = \sum_{j:\operatorname{\mathit{Fin}}\left(\mathit{dB}\right)}((\Vert\operatorname{\mathit{encoded}}\left(\mathit{Psi}, U, x\right)\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{mk}}\left(0, j\right)\right)\Vert)^{2})$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.unitaryVacuum` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Sum the squared moduli of the encoded coordinates whose Alice index is zero. This is the vacuum population of the reduced message state. Equation (3) requires this quantity to be at least 1 − omega for every input, where omega is the allowed energy and NeZero dA makes the vacuum index available.

**Definition 1.6 (Unassisted quantum communication with shared randomness).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall H \in \mathit{Type},\; \forall L \in \mathit{Type},\; \forall K \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(B\right)], [\operatorname{\mathit{NormedAddCommGroup}}\left(H\right)], [\operatorname{\mathit{InnerProductSpace}}\left(\mathit{Complex}, H\right)], [\operatorname{\mathit{CompleteSpace}}\left(H\right)], \forall vac \in H,\; \forall q \in L \to \mathit{Real},\; \forall p \in L \to \left(X \to \left(K \to \mathit{Real}\right)\right),\; \forall psi \in L \to \left(X \to \left(K \to H\right)\right),\; \forall N \in L \to \left(Y \to \left(B \to \operatorname{\mathit{ContinuousLinearMap}}\left(\mathit{Complex}, H, H\right)\right)\right),\; (\operatorname{\mathit{QCStrategy}}\left(\mathit{vac}, q, p, \mathit{psi}, N\right)) \Leftrightarrow ((\left\lVert \mathit{vac} \right\rVert = 1) \land ((\forall l \in L,\; 0 \le q\left(l\right)) \land ((\operatorname{\mathit{HasSum}}\left(q, 1\right)) \land ((\forall l \in L,\; \forall x \in X,\; \forall k \in K,\; 0 \le p\left(l, x, k\right)) \land ((\forall l \in L,\; \forall x \in X,\; \operatorname{\mathit{HasSum}}\left(p\left(l, x\right), 1\right)) \land ((\forall l \in L,\; \forall x \in X,\; \forall k \in K,\; \left\lVert \mathit{psi}\left(l, x, k\right) \right\rVert = 1) \land (\forall l \in L,\; \forall y \in Y,\; (\forall b \in B,\; 0 \le N\left(l, y, b\right)) \land (\sum_{b:B}(N\left(l, y, b\right)) = 1))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.QCStrategy` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

The message space H is an arbitrary complex Hilbert space with unit vacuum vector vac; there is no dimension restriction. Shared randomness ranges over an arbitrary type L, with nonnegative weights q and HasSum q 1. For each l and x, density operators enter through their ensemble decompositions: nonnegative weights p(l,x,k) with sum one and unit vectors psi(l,x,k), indexed by an arbitrary type K. Spectral decomposition represents every density operator in this way. For each l and y, N is a finite POVM of bounded complex linear operators; 0 ≤ N means positivity in the operator order. These are the states and measurements of the unassisted quantum model in Section II.B and Eq. (4). Bob retains no entangled system.

**Definition 1.7 (Probabilities averaged over the shared random variable).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; \forall H \in \mathit{Type},\; \forall L \in \mathit{Type},\; \forall K \in \mathit{Type},\; [\operatorname{\mathit{NormedAddCommGroup}}\left(H\right)], [\operatorname{\mathit{InnerProductSpace}}\left(\mathit{Complex}, H\right)], \forall q \in L \to \mathit{Real},\; \forall p \in L \to \left(X \to \left(K \to \mathit{Real}\right)\right),\; \forall psi \in L \to \left(X \to \left(K \to H\right)\right),\; \forall N \in L \to \left(Y \to \left(B \to \operatorname{\mathit{ContinuousLinearMap}}\left(\mathit{Complex}, H, H\right)\right)\right),\; \forall b \in B,\; \forall x \in X,\; \forall y \in Y,\; \operatorname{\mathit{qcProb}}\left(q, p, \mathit{psi}, N, b, x, y\right) = \operatorname{\mathit{tsum}}\left((l:L) \mapsto (q\left(l\right)) \cdot (\operatorname{\mathit{tsum}}\left((k:K) \mapsto (p\left(l, x, k\right)) \cdot (\operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{inner}}\left(\mathit{Complex}, \mathit{psi}\left(l, x, k\right), N\left(l, y, b\right)\left(\mathit{psi}\left(l, x, k\right)\right)\right)\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcProb` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Equation (4) averages the Born probabilities first over each message ensemble and then over shared randomness. For a density operator rho represented by an ensemble, Re Tr(N rho) is the weighted sum of Re inner(Complex,psi,N psi). The two tsum expressions range over the entire arbitrary index types L and K. The definition requires a complex inner-product space; positivity, normalization and completeness are supplied separately by QCStrategy.

**Definition 1.8 (The averaged vacuum population).**

$$\forall X \in \mathit{Type},\; \forall H \in \mathit{Type},\; \forall L \in \mathit{Type},\; \forall K \in \mathit{Type},\; [\operatorname{\mathit{NormedAddCommGroup}}\left(H\right)], [\operatorname{\mathit{InnerProductSpace}}\left(\mathit{Complex}, H\right)], \forall vac \in H,\; \forall q \in L \to \mathit{Real},\; \forall p \in L \to \left(X \to \left(K \to \mathit{Real}\right)\right),\; \forall psi \in L \to \left(X \to \left(K \to H\right)\right),\; \forall x \in X,\; \operatorname{\mathit{qcVacuum}}\left(\mathit{vac}, q, p, \mathit{psi}, x\right) = \operatorname{\mathit{tsum}}\left((l:L) \mapsto (q\left(l\right)) \cdot (\operatorname{\mathit{tsum}}\left((k:K) \mapsto (p\left(l, x, k\right)) \cdot (\left\lVert \operatorname{\mathit{inner}}\left(\mathit{Complex}, \mathit{vac}, \mathit{psi}\left(l, x, k\right)\right) \right\rVert^{2})\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.qcVacuum` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Equation (5) averages the squared vacuum overlaps over each message ensemble and over shared randomness, using tsum on both arbitrary index types. For unit vac, the ensemble average is the vacuum population of the corresponding density operator. The energy restriction is qcVacuum(vac,q,p,psi,x) at least 1 − omega for each x. It permits the conditional energies to differ. This expression is defined on any complex inner-product space without normalization assumptions.

**Definition 1.9 (A general finite linear communication task).**

$$\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(X\right)], [\operatorname{\mathit{Fintype}}\left(Y\right)], [\operatorname{\mathit{Fintype}}\left(B\right)], \forall c \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \forall p \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \operatorname{\mathit{taskValue}}\left(c, p\right) = \sum_{b:B}(\sum_{x:X}(\sum_{y:Y}((c\left(b, x, y\right)) \cdot (p\left(b, x, y\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.taskValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Each real coefficient c(b,x,y) multiplies the corresponding probability, and the sum includes all outcomes, inputs and settings. The coefficients are arbitrary; this includes success probabilities as well as other linear figures of merit.

**Definition 1.10 (The positive answer to the question for general tasks).**

$$(\mathit{claim}) \Leftrightarrow (\forall X \in \mathit{Type},\; \forall Y \in \mathit{Type},\; \forall B \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(X\right)], [\operatorname{\mathit{Fintype}}\left(Y\right)], [\operatorname{\mathit{Fintype}}\left(B\right)], \forall c \in B \to \left(X \to \left(Y \to \mathit{Real}\right)\right),\; \forall omega \in \mathit{Real},\; (0 \le \mathit{omega}) \Rightarrow ((\mathit{omega} < \frac{1}{2}) \Rightarrow (\forall dA \in \mathit{Nat},\; \forall dB \in \mathit{Nat},\; [\operatorname{\mathit{NeZero}}\left(\mathit{dA}\right)], \forall Psi \in \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right) \to \mathit{Complex},\; \forall U \in X \to \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \mathit{Complex}\right),\; \forall M \in Y \to \left(B \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(\mathit{dA}\right), \operatorname{\mathit{Fin}}\left(\mathit{dB}\right)\right), \mathit{Complex}\right)\right),\; (\operatorname{\mathit{UnitaryStrategy}}\left(\mathit{Psi}, U, M\right)) \Rightarrow ((\forall x \in X,\; 1 - \mathit{omega} \le \operatorname{\mathit{unitaryVacuum}}\left(\mathit{Psi}, U, x\right)) \Rightarrow (\exists H \in \mathit{Type},\; \exists [\operatorname{\mathit{NormedAddCommGroup}}\left(H\right)], \exists [\operatorname{\mathit{InnerProductSpace}}\left(\mathit{Complex}, H\right)], \exists [\operatorname{\mathit{CompleteSpace}}\left(H\right)], \exists vac \in H,\; \exists L \in \mathit{Type},\; \exists K \in \mathit{Type},\; \exists q \in L \to \mathit{Real},\; \exists p \in L \to \left(X \to \left(K \to \mathit{Real}\right)\right),\; \exists psi \in L \to \left(X \to \left(K \to H\right)\right),\; \exists N \in L \to \left(Y \to \left(B \to \operatorname{\mathit{ContinuousLinearMap}}\left(\mathit{Complex}, H, H\right)\right)\right),\; (\operatorname{\mathit{QCStrategy}}\left(\mathit{vac}, q, p, \mathit{psi}, N\right)) \land ((\forall x \in X,\; 1 - \mathit{omega} \le \operatorname{\mathit{qcVacuum}}\left(\mathit{vac}, q, p, \mathit{psi}, x\right)) \land (\operatorname{\mathit{taskValue}}\left(c, \operatorname{\mathit{unitaryProb}}\left(\mathit{Psi}, U, M\right)\right) \le \operatorname{\mathit{taskValue}}\left(c, \operatorname{\mathit{qcProb}}\left(q, p, \mathit{psi}, N\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim` (`✓ std3`).

*Citation.* Carles Roch i Carceller; Armin Tavakoli (2025). *The role of entanglement in energy-restricted communication and randomness generation*. DOI: [10.1088/2058-9565/ae4d80](https://doi.org/10.1088/2058-9565/ae4d80). URL: <https://arxiv.org/abs/2510.27473v1>.

*Commentary.*

Section VI asks whether unitary encoding remains resourceless for general tasks. The displayed proposition is the positive answer for finite alphabets and 0 ≤ omega < 1/2: every unitary entanglement-assisted value would be matched or exceeded by an unassisted strategy with the same energy bound. The latter may use any complex Hilbert message space with a unit vacuum vector, arbitrary shared randomness, density operators represented by ensembles, and POVMs of positive bounded operators. Its message dimension has no restriction. Result 4 concerns only probabilistic transmission of a bit; the proposition here quantifies over all finite linear tasks.

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

In every complex Hilbert space, unit vectors g and psi and an effect 0 ≤ E ≤ I satisfy Delta = Re inner(psi,E psi) − Re inner(g,E g) ≤ sqrt(1 − |inner(g,psi)|²). Multiply psi by a complex scalar of modulus one so that a = inner(g,psi) is real and nonnegative, and put u = psi + g and v = psi − g. Then Delta is both Re inner(u,E v) and −Re inner(u,(I − E)v). Cauchy–Schwarz for the positive forms of E and I − E gives Delta² ≤ A B and Delta² ≤ (U − A)(V − B), where A = inner(u,E u), B = inner(v,E v), U = norm(u)² = 2 + 2a and V = norm(v)² = 2 − 2a. The inequality sqrt(A B) + sqrt((U − A)(V − B)) ≤ sqrt(U V) yields the stated bound.

For nonnegative weights w summing to one and 0 ≤ t_j ≤ 1, put s = sum_j w_j t_j. Cauchy–Schwarz for sqrt(w_j) and sqrt(w_j t_j) gives sum_j w_j sqrt(t_j) = sum_j sqrt(w_j)·sqrt(w_j t_j) ≤ sqrt(sum_j w_j)·sqrt(sum_j w_j t_j) = sqrt(s). Apply this averaging bound to the ensemble decompositions of the density operators and then to shared randomness. The POVM identity gives sum_x inner(vac,N_x vac) = 1 for each value of the shared random variable. Consequently, in every Hilbert message space the four-guess task value is at most 1/4 + (1/4) sum_x sqrt(1 − qcVacuum(vac,q,p,psi,x)) ≤ 1/4 + sqrt(omega) under the same averaged energy restriction. Since sqrt(288/625) < 17/25, every such value is less than 93/100, whereas 2401/2500 > 93/100. Hence claim is false.

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
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
