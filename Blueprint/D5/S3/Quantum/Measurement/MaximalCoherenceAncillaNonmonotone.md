# An identity ancilla defeats maximal measurement coherence monotonicity

## Abstract

Maximal spectral-distance measurement coherence can increase under a CP unital map. The tetrahedral SIC qubit POVM has maximal coherence at most sqrt(2/3)/2, while adjoining an identity qubit gives maximal coherence at least 1/2.

**Definition 1.1 (Incoherent measurements).**

$$\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall B : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsIncoherent}\left(B\right) = \left((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(B\right)) \land (\forall x : \operatorname{Fin}\left(n\right), \operatorname{Matrix.IsDiag}\left((B\left(x\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.IsIncoherent` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Section II.A, p. 2: "In the same spirit, a quantum measurement is called incoherent when all its elements are diagonal in the reference basis:" The expression following this sentence is A_x = sum_i lambda_{i|x} |i><i|. Matrices have complex entries and outcomes are Fin n. The existing IsPOVM says that every effect is positive semidefinite and that their sum is the identity; IsDiag states diagonality in the reference coordinates.

**Definition 1.2 (The spectral distance).**

$$\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall B : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{dInf}\left(A, B\right) = \frac{1}{2} \cdot \sum_{x : \operatorname{Fin}\left(n\right)} \Vert A\left(x\right) - B\left(x\right) \Vert$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.dInf` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Equation (32), p. 5, at p = infinity is D_infinity(A,B) = (1/2) sum_x norm(A_x - B_x). Section IV.A, p. 7, adopts this distance. The norm is the spectral operator norm on Euclidean space, supplied by Matrix.Norms.L2Operator. This is the contractive distance of Tendick et al., Theorem 5, arXiv:2205.08546.

**Definition 1.3 (Coherence in a fixed basis).**

$$\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{coh}\left(A\right) = \operatorname{sInf}\left(\{r : \mathbb{R} \mid \exists B : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{IsIncoherent}\left(B\right)) \land (r = \operatorname{dInf}\left(A, B\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.coh` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Section II.A, p. 2: "A natural family of coherence monotones for measurements arises from a distance D between POVMs as" followed by C_D(A) = min_{B in I(d,n)} D(A,B). The encoding takes sInf of the corresponding set of real distances. The proof establishes nonemptiness and a lower bound for the four-outcome sets it uses.

**Definition 1.4 (Maximal coherence over reference bases).**

$$\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{cmax}\left(A\right) = \operatorname{sSup}\left(\{r : \mathbb{R} \mid \exists U : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (r = \operatorname{coh}\left((fun x : \operatorname{Fin}\left(n\right) \mapsto \operatorname{star}\left(U\right) \cdot A\left(x\right) \cdot U)\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.cmax` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Section III.A, p. 4: "Coherence is intrinsically basis dependent: rotating the reference basis by a unitary U alters the off-diagonal structure of every POVM element. We define the maximal coherence of measurement of 𝖠 as the basis-optimized value of any coherence monotone C_D," followed by C_D^max(A) = max_U C_D(U^dagger A U). The encoding takes sSup over Matrix.unitaryGroup, conjugating every effect by the same U. The proof bounds this set above and supplies the identity unitary as a member.

**Definition 1.5 (CP unital duals in Kraus form).**

$$\forall d : \mathbb{N}, \forall e : \mathbb{N}, \forall Phi : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right), \operatorname{IsCPUnitalDual}\left(Phi\right) = \exists k : \mathbb{N}, \exists K : \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right), (\sum_{j : \operatorname{Fin}\left(k\right)} \operatorname{Matrix.conjTranspose}\left((K\left(j\right))\right) \cdot K\left(j\right) = 1) \land (\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), Phi\left(X\right) = \sum_{j : \operatorname{Fin}\left(k\right)} \operatorname{Matrix.conjTranspose}\left((K\left(j\right))\right) \cdot X \cdot K\left(j\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.IsCPUnitalDual` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

In Eq. (12), p. 4, the source's preprocessing map is "the dual of an arbitrary CPTP quantum preprocessing channel" between "(possibly distinct) Hilbert spaces". Its finite-dimensional encoding uses k rectangular Kraus matrices K_j, with sum_j K_j^dagger K_j = I and Phi(X) = sum_j K_j^dagger X K_j. The dimensions d and e are independent.

**Definition 1.6 (The general monotonicity claim).**

$$claim = \forall d : \mathbb{N}, \forall e : \mathbb{N}, \forall n : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall Phi : \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right), \forall alpha : \mathbb{R}, \forall q : \operatorname{Fin}\left(n\right) \to \mathbb{R}, (2 < n) \Rightarrow ((\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)) \Rightarrow ((\operatorname{IsCPUnitalDual}\left(Phi\right)) \Rightarrow ((0 \le alpha) \Rightarrow ((alpha \le 1) \Rightarrow ((\forall x : \operatorname{Fin}\left(n\right), 0 \le q\left(x\right)) \Rightarrow ((\sum_{x : \operatorname{Fin}\left(n\right)} q\left(x\right) = 1) \Rightarrow (\operatorname{cmax}\left((fun x : \operatorname{Fin}\left(n\right) \mapsto \operatorname{SMul.smul}\left((alpha : \mathbb{C}), (Phi\left((A\left(x\right))\right))\right) + \operatorname{SMul.smul}\left(((1 - alpha) \cdot q\left(x\right) : \mathbb{C}), ((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right)))\right))\right) \le \operatorname{cmax}\left(A\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.claim` (`✓ std3`).

*Citation.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Section III.C, p. 7: "For non-dichotomic POVMs, the equivalence with sharpness is generally unavailable, and monotonicity must be considered at the channel level: it holds under mixed-unitary channels (Theorem 5) and under unitarily covariant channels (Corollary 6), but whether $\left(C_{D}\right)^{\operatorname{max}}$ remains monotonic under general CP unital maps in this regime is left as an open problem."

 Table I marks the non-dichotomic row under any fuzzifyng operations as Open. The encoding asks for every outcome count n > 2, every input and output dimension d and e, every POVM A, every CP unital dual Phi, every alpha in [0,1] and every probability distribution q, that the spectral-distance maximal coherence of the fuzzified effects is at most cmax A. The original labels 1,...,n become Fin n; no effect is omitted. Complex scalar casts of alpha and (1-alpha) q_x are explicit.

**Theorem 1.7 (General monotonicity fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result` (`✓ std3`). ∎

*Resolves.* `Problems/baek-jo-nha-2026-maximal-coherence-monotonicity` (refuted) by `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baek-jo-nha-2026-maximal-coherence-monotonicity","declaration_gid":"D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Baek; Y. Jo; H. Nha (2026). *Maximal coherence of quantum measurement and the resource theory of sharpness*. URL: <https://arxiv.org/abs/2607.05847v1>.

*Commentary.*

Take d = 2, e = 4, n = 4, alpha = 1 and q_x = 1/4. The effects are A_i = (I + n_i dot sigma)/4, with tetrahedral vectors (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1) divided by sqrt(3). The identification of C^2 tensor C^2 with Fin 4 is finProdFinEquiv: (i,j) maps to 2*i+j, ordered |00>, |01>, |10>, |11>. The discarding dual J(X) = X tensor I_2 has two Kraus matrices and is unital. For every qubit unitary, dephasing is an incoherent POVM and the four squared off-diagonal moduli sum to 1/6. Cauchy-Schwarz gives cmax A <= sqrt(2/3)/2. In the Bell basis, every diagonal competitor has scalar normalized partial trace. Applying the Rayleigh bound to a difference and its negative, using eigenvalues 1/2 and 0 of each SIC effect, gives a norm lower bound 1/4 per effect and hence cmax(J(A)) >= 1/2. Since sqrt(2/3)/2 < 1/2, claim is false. This settles the dimension-changing spectral-distance case. The source's dichotomic, mixed-unitary and covariant conclusions retain their hypotheses. Diamond distance and dimension-preserving monotonicity remain open.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.IsCPUnitalDual`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.IsIncoherent`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.cmax`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.coh`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.dInf`
- Truth anchor: `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result`
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
