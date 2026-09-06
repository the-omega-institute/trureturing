# Finite Icosahedral Axis Decomposition

## Abstract

The finite icosahedral action partitions the projective plane over F5 into its three axis orbits.

**Theorem 1.1 (The projective axes split into the fivefold, threefold, and twofold orbits).**

$$\begin{gathered}\operatorname{Disjoint}\left(\mathcal{A}_{5}, \mathcal{A}_{3}\right) \land \operatorname{Disjoint}\left(\mathcal{A}_{5}, \mathcal{A}_{2}\right) \land \operatorname{Disjoint}\left(\mathcal{A}_{3}, \mathcal{A}_{2}\right) \land\\{}\operatorname{union}\left(\mathcal{A}_{5}, \mathcal{A}_{3}, \mathcal{A}_{2}\right) = \mathbb{P}^{2}(\mathbb{F}_{5}) \land\\{}\lvert \mathcal{A}_{5} \rvert = 6 \land \lvert \mathcal{A}_{3} \rvert = 10 \land \lvert \mathcal{A}_{2} \rvert = 15 \land\\{}(\forall p \in \mathcal{A}_{5},\ \operatorname{orbit}\left(p\right) = \mathcal{A}_{5}) \land\\{}(\forall p \in \mathcal{A}_{3},\ \operatorname{orbit}\left(p\right) = \mathcal{A}_{3}) \land\\{}(\forall p \in \mathcal{A}_{2},\ \operatorname{orbit}\left(p\right) = \mathcal{A}_{2}) \land\\{}(\forall p \in \mathcal{A}_{5},\ \lvert \operatorname{Stab}\left(p\right) \rvert = 10) \land\\{}(\forall p \in \mathcal{A}_{3},\ \lvert \operatorname{Stab}\left(p\right) \rvert = 6) \land\\{}(\forall p \in \mathcal{A}_{2},\ \lvert \operatorname{Stab}\left(p\right) \rvert = 4) \land\\{}(\forall p \in \mathcal{A}_{5},\ \lvert \operatorname{C5}\left(p\right) \rvert = 5 \land \operatorname{Cyclic}\left(\operatorname{C5}\left(p\right)\right) \land \operatorname{Stab}\left(p\right) = \operatorname{Normalizer}\left(\operatorname{C5}\left(p\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition.finite_icosahedral_axis_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is Mathlib's projectivization of the three-dimensional vector space over F5. Its cardinality 31 is derived from the projectivization cardinality theorem, and a proved equivalence to the 31-entry coordinate chart transports the finite computation.

The source quadratic form defines three concrete classes in the actual projective plane. They are pairwise disjoint, their union is the whole projective plane, and their cardinalities are 6, 10, and 15.

The two source matrices define a linear A5 action, and Mathlib induces its action on projectivization. The coordinate equivalence is proved equivariant for this action; every class is one orbit, with stabilizer cardinalities 10, 6, and 4.

For every fivefold axis, the subgroup of stabilizing rotations whose fifth power is the identity has cardinality 5 and is cyclic. The axis stabilizer is exactly the normalizer of this subgroup.

## References

- Truth anchor: `D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition.finite_icosahedral_axis_decomposition`
