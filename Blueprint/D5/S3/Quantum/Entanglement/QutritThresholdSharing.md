# Qutrit Threshold Sharing

## Abstract

The three-qutrit threshold encoding hides the input in every single share and recovers it from each pair by an explicit permutation unitary.

All share and input labels lie in ZMod 3, so every label operation is modulo three. Amplitudes are complex numbers. V denotes qutritEncoding, and the coordinate, marginal, and decoder declarations are cyclicShares, singleShareMarginal, and qutritDecoder. Tuples use Lean's right-associated product. The operator Complex.ofReal is the canonical inclusion from real to complex numbers; sqrt is the nonnegative real square root. All displayed fractions are complex-field division.

**Definition 1.1 (The common three-share encoding).**

$$\forall q \in \operatorname{ZMod}(3) \times (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)),\; \forall s \in \operatorname{ZMod}(3),\; V(q, s) = \frac{1}{\operatorname{Complex.ofReal}(\sqrt{3})} \cdot \sum_{j: \operatorname{ZMod}(3)} (\operatorname{ite}(q = (j, j + s, j + 2 \cdot s), 1, 0))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutritEncoding` (`✓ std3`).

*Citation.* Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo (1999). *How to share a quantum secret*. DOI: [10.1103/PhysRevLett.83.648](https://doi.org/10.1103/PhysRevLett.83.648).

*Commentary.*

V is a matrix over the complex numbers with row labels in ZMod 3 x ZMod 3 x ZMod 3 and column labels in ZMod 3. The finite sum is the defining expression, with ite taking its condition, true value, and false value in that order.

**Definition 1.2 (Cyclic coordinate orders).**

$$\forall i \in \operatorname{Fin}(3),\; \forall q \in \operatorname{ZMod}(3) \times (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)),\; \operatorname{cyclicShares}(i, q) = \operatorname{ite}(i = 0, q, \operatorname{ite}(i = 1, (\left(q_{2}\right)_{2}, q_{1}, \left(q_{2}\right)_{1}), (\left(q_{2}\right)_{1}, \left(q_{2}\right)_{2}, q_{1})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritThresholdSharing.cyclicShares` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index i has type Fin 3. cyclicShares(i,q) inserts the ordered decoder inputs and spectator into the original coordinates. Indices 0, 1, 2 select ordered pairs (1,2), (2,3), (3,1), respectively; retaining the first argument retains original share 1, 2, 3, respectively. This helper is the coordinate adapter used by both theorems.

**Definition 1.3 (Partial trace retaining the selected share).**

$$\forall i \in \operatorname{Fin}(3),\; \forall M \in \operatorname{Matrix}(\operatorname{ZMod}(3) \times (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)), \operatorname{ZMod}(3) \times (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)), \mathbb{C}),\; \operatorname{singleShareMarginal}(i, M) = \operatorname{partialTraceFirst}((p: (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)) \times \operatorname{ZMod}(3) \mapsto (q: (\operatorname{ZMod}(3) \times \operatorname{ZMod}(3)) \times \operatorname{ZMod}(3) \mapsto M(\operatorname{cyclicShares}(i, (p_{2}, \left(p_{1}\right)_{1}, \left(p_{1}\right)_{2})), \operatorname{cyclicShares}(i, (q_{2}, \left(q_{1}\right)_{1}, \left(q_{1}\right)_{2}))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritThresholdSharing.singleShareMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singleShareMarginal(i,M) is a matrix over the complex numbers with both row and column labels in ZMod 3. The formula is the defining application of the frozen partialTraceFirst, which sums over equal first-factor indices. In the displayed lambda, p and q have type (ZMod 3 x ZMod 3) x ZMod 3; subscripts denote product projections.

**Definition 1.4 (The explicit decoder and its inverse).**

$$\forall p \in \operatorname{ZMod}(3) \times \operatorname{ZMod}(3),\; (qutritDecoder(p) = (p_{2} - p_{1}, 2 \cdot p_{2} - p_{1})) \land (qutritDecoder^{-1}(p) = (p_{2} - 2 \cdot p_{1}, p_{2} - p_{1}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutritDecoder` (`✓ std3`).

*Citation.* Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo (1999). *How to share a quantum secret*. DOI: [10.1103/PhysRevLett.83.648](https://doi.org/10.1103/PhysRevLett.83.648).

*Commentary.*

qutritDecoder is an Equiv.Perm (ZMod 3 x ZMod 3). Its toFun and invFun are the two displayed expressions; the left and right inverse laws are proved by ring arithmetic inside this definition. For column amplitudes, Equiv.Perm.permMatrix applied over the complex numbers to the inverse of qutritDecoder has entry one at (x,y) exactly when y = qutritDecoder.symm(x), and zero otherwise. Its action on a basis vector labelled y therefore yields the basis vector labelled qutritDecoder(y). A star superscript denotes conjugate transpose.

**Theorem 1.5 (Partial trace on every matrix unit).**

$$\forall i \in \operatorname{Fin}(3),\; \forall s \in \operatorname{ZMod}(3),\; \forall t \in \operatorname{ZMod}(3),\; \operatorname{singleShareMarginal}(i, V \cdot \operatorname{single}(s, t, 1) \cdot V^{*}) = \operatorname{ite}(s = t, \frac{1}{3}, 0) \cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_matrix_unit_marginal` (`✓ std3`). ∎

*Citation.* Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo (1999). *How to share a quantum secret*. DOI: [10.1103/PhysRevLett.83.648](https://doi.org/10.1103/PhysRevLett.83.648).

*Commentary.*

single(s,t,1) is the standard Matrix.single s t with complex entry one, and I is the three-dimensional identity matrix. The proof uses the index system j+s=k+t and j+2s=k+2t, which forces s=t and j=k. Cyclic symmetry extends the calculation to all three shares.

**Theorem 1.6 (Every single share is maximally mixed).**

$$\forall rho \in \operatorname{DensityState}(\operatorname{ZMod}(3)),\; \forall i \in \operatorname{Fin}(3),\; \operatorname{singleShareMarginal}(i, V \cdot \operatorname{val}(rho) \cdot V^{*}) = \frac{1}{3} \cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_single_share_maximally_mixed` (`✓ std3`). ∎

*Citation.* Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo (1999). *How to share a quantum secret*. DOI: [10.1103/PhysRevLett.83.648](https://doi.org/10.1103/PhysRevLett.83.648).

*Commentary.*

rho ranges over the canonical FiniteStateChannel.DensityState (ZMod 3): positive complex matrices of trace one. val(rho) denotes exactly CStarMatrix.ofMatrix.symm rho.1, the underlying ordinary matrix. Linearity and the frozen trace-one theorem extend the matrix-unit calculation to every input state, including mixed states.

**Theorem 1.7 (Every pair reconstructs every input amplitude).**

$$\forall psi \in (\operatorname{ZMod}(3) \to \mathbb{C}),\; \forall i \in \operatorname{Fin}(3),\; \forall r \in \operatorname{ZMod}(3),\; \operatorname{mulVec}(\operatorname{Equiv.Perm.permMatrix}(\mathbb{C}, qutritDecoder^{-1}), (p: \operatorname{ZMod}(3) \times \operatorname{ZMod}(3) \mapsto \operatorname{mulVec}(V, psi)(\operatorname{cyclicShares}(i, (p_{1}, p_{2}, r))))) = (p: \operatorname{ZMod}(3) \times \operatorname{ZMod}(3) \mapsto psi(p_{1}) \cdot (\frac{1}{\operatorname{Complex.ofReal}(\sqrt{3})} \cdot \sum_{j: \operatorname{ZMod}(3)} (\operatorname{ite}((p_{2}, r) = (j, j), 1, 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_two_share_reconstruction` (`✓ std3`). ∎

*Citation.* Richard Cleve, Daniel Gottesman, and Hoi-Kwong Lo (1999). *How to share a quantum secret*. DOI: [10.1103/PhysRevLett.83.648](https://doi.org/10.1103/PhysRevLett.83.648).

*Commentary.*

mulVec is ordinary matrix action on column amplitudes. Both sides are functions of p in ZMod 3 x ZMod 3. The spectator label r is universally quantified, so this is equality of all three-share amplitudes after decoding. The input psi is arbitrary, hence the identity applies in particular to every normalized pure state. The output is psi tensor the fixed normalized sum of |j,j>. All three choices of i use the same encoding and decoder.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.cyclicShares`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutritDecoder`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutritEncoding`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_matrix_unit_marginal`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_single_share_maximally_mixed`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.qutrit_two_share_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritThresholdSharing.singleShareMarginal`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
