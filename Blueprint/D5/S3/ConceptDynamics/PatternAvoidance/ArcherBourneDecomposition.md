# Archer-Bourne Decomposition

## Abstract

The permutations avoiding 312 and 321 are exactly the direct sums of cyclic rotations indexed by compositions, and the cube criterion gives the corresponding counting identity.

**Definition 1.1 (The pattern 312).**

$$p_{312} : Perm\left(Fin\left(3\right)\right) := [2, 0, 1].$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.pattern312` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

The zero-based values two, zero, one define the permutation pattern 312.

**Definition 1.2 (The pattern 321).**

$$p_{321} : Perm\left(Fin\left(3\right)\right) := [2, 1, 0].$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.pattern321` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

The zero-based values two, one, zero define the permutation pattern 321.

**Definition 1.3 (Avoidance of 312).**

$$\forall n \in \mathbb{N}, \forall \pi \in Perm\left(Fin\left(n\right)\right), \left(Avoids_{312}\right)\left(\pi\right) := \neg Contains\left(p_{312}, \pi\right).$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.Avoids312` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

This is the negation of the generic pattern-containment predicate at the permutation 312.

**Definition 1.4 (Avoidance of 321).**

$$\forall n \in \mathbb{N}, \forall \pi \in Perm\left(Fin\left(n\right)\right), \left(Avoids_{321}\right)\left(\pi\right) := \neg Contains\left(p_{321}, \pi\right).$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.Avoids321` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

This is the negation of the generic pattern-containment predicate at the permutation 321.

**Theorem 1.5 (Positive rotation sums avoid both patterns).**

$$\forall d \in List\left(\mathbb{N}\right), (\forall i \in Fin\left(length\left(d\right)\right), 0 < d_{i}) \Rightarrow (\left(Avoids_{312}\right)\left(rotationSumPerm\left(d\right)\right) \land \left(Avoids_{321}\right)\left(rotationSumPerm\left(d\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumPerm_avoids_312_321` (`✓ std3`). ∎

*Citation.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

A list of positive block sizes determines a direct sum of cyclic rotations. Archer and Bourne's Lemma 3.1 gives the avoidance direction of this characterization.

**Definition 1.6 (Rotation sum indexed by a composition).**

$$\forall n \in \mathbb{N}, \forall c \in Composition\left(n\right), rotationSumComposition\left(c\right): Perm\left(Fin\left(n\right)\right) := transport\left(rotationSumPerm\left(blocks\left(c\right)\right)\right)_{\sum_{i \in Fin\left(length\left(blocks\left(c\right)\right)\right)} blocks\left(c\right)_{i} = n}.$$

*Formalization.* `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

The sum equation carried by a Mathlib composition transports the list-level rotation sum to a permutation of the required finite interval.

**Theorem 1.7 (Every composition gives an avoider).**

$$\forall n \in \mathbb{N}, \forall c \in Composition\left(n\right), \left(Avoids_{312}\right)\left(rotationSumComposition\left(c\right)\right) \land \left(Avoids_{321}\right)\left(rotationSumComposition\left(c\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition_avoids_312_321` (`✓ std3`). ∎

*Citation.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

Every block of a composition is positive, so the associated rotation sum avoids both 312 and 321.

**Theorem 1.8 (Archer-Bourne decomposition).**

$$\forall n \in \mathbb{N}, \forall \pi \in Perm\left(Fin\left(n\right)\right), (\left(Avoids_{312}\right)\left(\pi\right) \land \left(Avoids_{321}\right)\left(\pi\right)) \Leftrightarrow (\exists c \in Composition\left(n\right), \pi = rotationSumComposition\left(c\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.avoids_312_321_iff_exists_rotationSumComposition` (`✓ std3`). ∎

*Citation.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

A permutation avoids 312 and 321 exactly when it is the direct sum of the cyclic rotations determined by a composition of its size. This is Archer and Bourne's Lemma 3.1.

**Theorem 1.9 (Uniqueness of the composition).**

$$\forall n \in \mathbb{N}, \forall c, e \in Composition\left(n\right), rotationSumComposition\left(c\right) = rotationSumComposition\left(e\right) \Rightarrow c = e.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition_injective` (`✓ std3`). ∎

*Citation.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

The boundary set consists of zero and exactly the positions x + 1 for which pi(x) <= x. Equal rotation sums therefore have equal compositions; together with the decomposition theorem, this is the bijection identified after Lemma 3.1.

**Theorem 1.10 (The Archer-Bourne counting equality).**

$$\forall n \in \mathbb{N}, card\left(\{\pi \in Perm\left(Fin\left(n\right)\right) : \left(Avoids_{312}\right)\left(\pi\right) \land \left(Avoids_{321}\right)\left(\pi\right) \land \neg \left(Contains_{2143}\right)\left(\pi^{3}\right)\}\right) = card\left(\{c \in Composition\left(n\right) : card\left(\{i \in Fin\left(length\left(blocks\left(c\right)\right)\right) : blocks\left(c\right)_{i} \neq 1 \land blocks\left(c\right)_{i} \neq 3\}\right) \leq 1\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.card_avoids_312_321_cube_2143_eq_compositions` (`✓ std3`). ∎

*Resolves.* `Problems/archer-bourne-cube-2143-count` (proved) by `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.card_avoids_312_321_cube_2143_eq_compositions`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-bourne-cube-2143-count","declaration_gid":"D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.card_avoids_312_321_cube_2143_eq_compositions","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199).

*Commentary.*

The decomposition and its uniqueness identify the 312/321 avoiders with compositions. The frozen cube criterion restricts this bijection on both sides to exactly the displayed exceptional-part condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.Avoids312`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.Avoids321`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.avoids_312_321_iff_exists_rotationSumComposition`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.card_avoids_312_321_cube_2143_eq_compositions`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.pattern312`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.pattern321`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition_avoids_312_321`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumComposition_injective`
- Truth anchor: `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.rotationSumPerm_avoids_312_321`
- Dependency: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](../../../S1/Words/Patterns/DerangementRatioNonconvergence.md)
- Dependency: [D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance](RotationSumPowerPatternAvoidance.md)
