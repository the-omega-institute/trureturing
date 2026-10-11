# Qubit Incompatibility Rigidity

## Abstract

Restricted-state compatibility determines incompatible unbiased qubit pairs.

**Definition 1.1 (Bloch vector space).**

$$(V: Type) = \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch vectors form real Euclidean three-space.

**Definition 1.2 (Density matrices).**

$$(Density: Type) = \{(rho: QubitMatrix) | (\operatorname{Matrix.PosSemidef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = (1: \mathbb{C}))\}$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A density matrix is positive semidefinite and has complex trace one. The subtype projection val returns its matrix.

**Definition 1.3 (The second Pauli matrix).**

$$(pauliY: QubitMatrix) = \begin{pmatrix}0&-\operatorname{Complex.I}\\\operatorname{Complex.I}&0\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.pauliY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The off-diagonal entries are minus i and i.

**Definition 1.4 (Pauli expansion).**

$$\forall v \in V,\; \operatorname{pauli}\left(v\right) = ((v\left(0\right): \mathbb{C})) \cdot (qubitX) + ((v\left(1\right): \mathbb{C})) \cdot (pauliY) + ((v\left(2\right): \mathbb{C})) \cdot (qubitZ)$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.pauli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three real coordinates are coerced to complex scalars acting on the Pauli matrices.

**Definition 1.5 (Unbiased effects).**

$$\forall v \in V,\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{effect}\left(v, s\right) = ((\frac{1}{2}: \mathbb{C})) \cdot ((1: QubitMatrix) + (\operatorname{ite}\left(s = (0: \operatorname{Fin}\left(2\right)), (1: \mathbb{C}), (-1: \mathbb{C})\right)) \cdot (\operatorname{pauli}\left(v\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Outcome zero uses the positive Pauli expansion; outcome one uses its negative. One half is a complex scalar.

**Definition 1.6 (A joint POVM).**

$$\forall G \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to QubitMatrix,\; (\operatorname{IsPOVM}\left(G\right)) \Leftrightarrow ((\forall q \in \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right),\; \operatorname{Matrix.PosSemidef}\left(G\left(q\right)\right)) \land (\sum_{(s: \operatorname{Fin}\left(2\right))} (\sum_{(t: \operatorname{Fin}\left(2\right))} (G\left((s, t)\right))) = (1: QubitMatrix)))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.IsPOVM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four positive effects sum to the identity matrix.

**Definition 1.7 (Marginal effects).**

$$\forall G \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to QubitMatrix,\; \forall i \in \operatorname{Fin}\left(2\right),\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{marginal}\left(G, i, s\right) = \operatorname{ite}\left(i = (0: \operatorname{Fin}\left(2\right)), \sum_{(t: \operatorname{Fin}\left(2\right))} (G\left((s, t)\right)), \sum_{(t: \operatorname{Fin}\left(2\right))} (G\left((t, s)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.marginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first marginal sums over the second outcome, and the second marginal sums over the first outcome.

**Definition 1.8 (Compatibility on a state set).**

$$\forall S \in \operatorname{Set}\left(Density\right),\; \forall a \in \operatorname{Fin}\left(2\right) \to V,\; (\operatorname{SCompatible}\left(S, a\right)) \Leftrightarrow (\exists G \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to QubitMatrix,\; (\operatorname{IsPOVM}\left(G\right)) \land (\forall rho \in Density,\; (rho \in S) \Rightarrow (\forall i \in \operatorname{Fin}\left(2\right),\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{bornProbability}\left(\operatorname{val}\left(rho\right), \operatorname{marginal}\left(G, i, s\right)\right) = \operatorname{bornProbability}\left(\operatorname{val}\left(rho\right), \operatorname{effect}\left(a\left(i\right), s\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A joint POVM reproduces both observable distributions on every density matrix in the given state set. bornProbability is the complex trace of the matrix product.

**Definition 1.9 (Incompatibility).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to V,\; (\operatorname{Incompatible}\left(a\right)) \Leftrightarrow (\neg (\operatorname{SCompatible}\left((\operatorname{Set.univ}: \operatorname{Set}\left(Density\right)), a\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Incompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No joint POVM reproduces both observables on the set of all density matrices.

**Definition 1.10 (Signs and exchange).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to V,\; \forall b \in \operatorname{Fin}\left(2\right) \to V,\; (\operatorname{SignedPermutation}\left(a, b\right)) \Leftrightarrow (\exists pi \in \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right),\; \exists eps \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(2\right),\; (eps\left(i\right) = 1) \lor (eps\left(i\right) = -1)) \land (\forall i \in \operatorname{Fin}\left(2\right),\; b\left(i\right) = (eps\left(i\right)) \cdot (a\left(pi\left(i\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SignedPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each vector may be negated independently, and the two observables may be exchanged.

**Definition 1.11 (Rigidity statement).**

$$(claim) \Leftrightarrow (\forall a \in \operatorname{Fin}\left(2\right) \to V,\; \forall b \in \operatorname{Fin}\left(2\right) \to V,\; (\forall i \in \operatorname{Fin}\left(2\right),\; \left\lVert a\left(i\right) \right\rVert \le 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(2\right),\; \left\lVert b\left(i\right) \right\rVert \le 1) \Rightarrow ((\operatorname{Incompatible}\left(a\right)) \Rightarrow ((\operatorname{Incompatible}\left(b\right)) \Rightarrow ((\forall S \in \operatorname{Set}\left(Density\right),\; (\operatorname{SCompatible}\left(S, a\right)) \Leftrightarrow (\operatorname{SCompatible}\left(S, b\right))) \Leftrightarrow (\operatorname{SignedPermutation}\left(a, b\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Torii; R. Takakura; R. Imamura (2025). *Comparing quantum incompatibility of device sets from an operational perspective*. DOI: [10.1103/s6mc-lnvl](https://doi.org/10.1103/s6mc-lnvl). URL: <https://arxiv.org/abs/2509.08284v2>.

*Commentary.*

In §IV.A, Proposition 7 of Torii, Takakura and Imamura states: “Let A_ub = {A^{a_1}_ub, A^{a_2}_ub} and B_ub = {A^{b_1}_ub, A^{b_2}_ub} be pairs of unbiased qubit observables satisfying |a_1|=|a_2|=t, |b_1|=|b_2|=u for some t,u ∈ (1/√2,1]. If A_ub ∼_inc B_ub, then either (b_1,b_2) = (±a_1,±a_2) or (b_1,b_2) = (±a_2,±a_1) holds.” The statement here allows arbitrary individual lengths at most one and assumes that each pair is incompatible.

**Theorem 1.12 (Rigidity without equal-length constraints).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Torii; R. Takakura; R. Imamura (2025). *Comparing quantum incompatibility of device sets from an operational perspective*. DOI: [10.1103/s6mc-lnvl](https://doi.org/10.1103/s6mc-lnvl). URL: <https://arxiv.org/abs/2509.08284v2>.

*Commentary.*

In §V, the authors ask: “Future work will also address the generalization of Proposition 7, as it remains an open problem whether the result holds without the constraints of |a_1|=|a_2| and |b_1|=|b_2|.” For incompatible pairs, equality of compatibility on every state set determines the two Bloch vectors up to independent signs and exchange. Central Bloch disks determine a quartic boundary. Equality of these boundaries forces a common plane, and polynomial identities force the coordinate change to be a signed permutation. Conversely, outcome relabelling and exchange preserve compatibility on every state set.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Density`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Incompatible`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.IsPOVM`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SCompatible`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SignedPermutation`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.V`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.effect`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.marginal`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.pauli`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.pauliY`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddingMap](../../Arith/Lattices/Klartag/State/PaddingMap.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
