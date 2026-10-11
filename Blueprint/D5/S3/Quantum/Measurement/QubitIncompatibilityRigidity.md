# Qubit Incompatibility Rigidity

## Abstract

Restricted-state compatibility determines incompatible unbiased qubit pairs.

**Definition 1.1 (Unbiased effects).**

$$\forall v \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{effect}\left(v, s\right) = ((\frac{1}{2}: \mathbb{C})) \cdot ((1: QubitMatrix) + (\operatorname{ite}\left(s = (0: \operatorname{Fin}\left(2\right)), (1: \mathbb{C}), (-1: \mathbb{C})\right)) \cdot (\operatorname{FourQubitParentConstruction.B}\left(v\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FourQubitParentConstruction.B expands a Bloch vector in the three Pauli matrices. Outcome zero uses that expansion and outcome one uses its negative. One half is a complex scalar.

**Definition 1.2 (Marginal effects).**

$$\forall G \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to QubitMatrix,\; \forall i \in \operatorname{Fin}\left(2\right),\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{marginal}\left(G, i, s\right) = \operatorname{ite}\left(i = (0: \operatorname{Fin}\left(2\right)), \sum_{(t: \operatorname{Fin}\left(2\right))} (G\left((s, t)\right)), \sum_{(t: \operatorname{Fin}\left(2\right))} (G\left((t, s)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.marginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first marginal sums over the second outcome, and the second marginal sums over the first outcome.

**Definition 1.3 (Compatibility on a state set).**

$$\forall S \in \operatorname{Set}\left(\operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right)\right),\; \forall a \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; (\operatorname{SCompatible}\left(S, a\right)) \Leftrightarrow (\exists G \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to QubitMatrix,\; (\operatorname{ConcealmentKernelNecessityRefutation.IsPOVM}\left(G\right)) \land (\forall rho \in \operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; (rho \in S) \Rightarrow (\forall i \in \operatorname{Fin}\left(2\right),\; \forall s \in \operatorname{Fin}\left(2\right),\; \operatorname{bornProbability}\left(\operatorname{Equiv.symm}\left(\operatorname{CStarMatrix.ofMatrix}\right)\left(\operatorname{val}\left(rho\right)\right), \operatorname{marginal}\left(G, i, s\right)\right) = \operatorname{bornProbability}\left(\operatorname{Equiv.symm}\left(\operatorname{CStarMatrix.ofMatrix}\right)\left(\operatorname{val}\left(rho\right)\right), \operatorname{effect}\left(a\left(i\right), s\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ConcealmentKernelNecessityRefutation.IsPOVM requires positive semidefinite effects summing to the identity. States use FiniteStateChannel.DensityState on Fin 2, whose underlying matrices are positive semidefinite with trace one. A joint POVM reproduces both observable distributions on every state in the given set. CStarMatrix.ofMatrix.symm returns the underlying matrix, and bornProbability is the complex trace of the matrix product.

**Definition 1.4 (Incompatibility).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; (\operatorname{Incompatible}\left(a\right)) \Leftrightarrow (\neg (\operatorname{SCompatible}\left((\operatorname{Set.univ}: \operatorname{Set}\left(\operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right)\right)), a\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Incompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No joint POVM reproduces both observables on the set of all density matrices.

**Definition 1.5 (Signs and exchange).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall b \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; (\operatorname{SignedPermutation}\left(a, b\right)) \Leftrightarrow (\exists pi \in \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right),\; \exists eps \in \operatorname{Fin}\left(2\right) \to \mathbb{R},\; (\forall i \in \operatorname{Fin}\left(2\right),\; (eps\left(i\right) = 1) \lor (eps\left(i\right) = -1)) \land (\forall i \in \operatorname{Fin}\left(2\right),\; b\left(i\right) = (eps\left(i\right)) \cdot (a\left(pi\left(i\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SignedPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each vector may be negated independently, and the two observables may be exchanged.

**Definition 1.6 (Rigidity statement).**

$$(claim) \Leftrightarrow (\forall a \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall b \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; (\forall i \in \operatorname{Fin}\left(2\right),\; \left\lVert a\left(i\right) \right\rVert \le 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(2\right),\; \left\lVert b\left(i\right) \right\rVert \le 1) \Rightarrow ((\operatorname{Incompatible}\left(a\right)) \Rightarrow ((\operatorname{Incompatible}\left(b\right)) \Rightarrow ((\forall S \in \operatorname{Set}\left(\operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right)\right),\; (\operatorname{SCompatible}\left(S, a\right)) \Leftrightarrow (\operatorname{SCompatible}\left(S, b\right))) \Leftrightarrow (\operatorname{SignedPermutation}\left(a, b\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.claim` (`✓ std3`).

*Citation.* K. Torii; R. Takakura; R. Imamura (2025). *Comparing quantum incompatibility of device sets from an operational perspective*. DOI: [10.1103/s6mc-lnvl](https://doi.org/10.1103/s6mc-lnvl). URL: <https://arxiv.org/abs/2509.08284v2>.

*Commentary.*

In §IV.A, Proposition 7 of Torii, Takakura and Imamura states: “Let A_ub = {A^{a_1}_ub, A^{a_2}_ub} and B_ub = {A^{b_1}_ub, A^{b_2}_ub} be pairs of unbiased qubit observables satisfying |a_1|=|a_2|=t, |b_1|=|b_2|=u for some t,u ∈ (1/√2,1]. If A_ub ∼_inc B_ub, then either (b_1,b_2) = (±a_1,±a_2) or (b_1,b_2) = (±a_2,±a_1) holds.” The statement here allows arbitrary individual lengths at most one and assumes that each pair is incompatible.

**Theorem 1.7 (Rigidity without equal-length constraints).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result` (`✓ std3`). ∎

*Resolves.* `Problems/torii-takakura-imamura-2025-proposition-7-generalization` (proved) by `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"torii-takakura-imamura-2025-proposition-7-generalization","declaration_gid":"D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Torii; R. Takakura; R. Imamura (2025). *Comparing quantum incompatibility of device sets from an operational perspective*. DOI: [10.1103/s6mc-lnvl](https://doi.org/10.1103/s6mc-lnvl). URL: <https://arxiv.org/abs/2509.08284v2>.

*Commentary.*

In §V, the authors ask: “Future work will also address the generalization of Proposition 7, as it remains an open problem whether the result holds without the constraints of |a_1|=|a_2| and |b_1|=|b_2|.” For incompatible pairs, equality of compatibility on every state set determines the two Bloch vectors up to independent signs and exchange. Central Bloch disks determine a quartic boundary. Equality of these boundaries forces a common plane, and polynomial identities force the coordinate change to be a signed permutation. Conversely, outcome relabelling and exchange preserve compatibility on every state set.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.Incompatible`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SCompatible`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.SignedPermutation`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.effect`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.marginal`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.result`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddingMap](../../Arith/Lattices/Klartag/State/PaddingMap.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
