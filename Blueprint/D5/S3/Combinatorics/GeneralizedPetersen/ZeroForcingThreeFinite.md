# Forts and Mask Completeness

## Abstract

The numeric predicates agree with graph neighborhoods, vertex sets, and complete initial-force families.

**Definition 1.1 (Finite graph neighborhood).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall v \in V,\; \operatorname{Finite}\left(V\right) \Rightarrow \operatorname{finiteNeighbors}\left(G, v\right) = \{ w \in V| \operatorname{Adj}\left(G, v, w\right)\} $$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.finiteNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For a finite simple graph, the neighborhood consists of exactly the adjacent vertices.

**Definition 1.2 (A set that resists forcing).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall F \in \operatorname{Finset}\left(V\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\operatorname{IsFort}\left(G, F\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(F\right) \land \left(\forall v \in V,\; \left(\neg v \in F\right) \Rightarrow \operatorname{card}\left(\operatorname{inter}\left(\operatorname{finiteNeighbors}\left(G, v\right), F\right)\right) \ne 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.IsFort` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A fort is nonempty, and no vertex outside it has exactly one neighbor in it.

**Theorem 1.3 (Agreement of the neighbor table).**

$$\forall v \in \mathrm{V13},\; \forall w \in \mathrm{V13},\; w \in \operatorname{neighbors13}\left(v\right) \Leftrightarrow \operatorname{Adj}\left(\operatorname{gp}\left(13, 3\right), v, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.neighbors13_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The three listed neighbors are exactly the graph neighbors in P(13,3).

**Theorem 1.4 (Bits count decoded vertices).**

$$\forall m \in \mathrm{Nat},\; \operatorname{bitCount26}\left(m\right) = \operatorname{card}\left(\operatorname{maskSet13}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.bitCount26_eq_card_maskSet13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The number of low set bits equals the cardinality of the decoded vertex set.

**Theorem 1.5 (A valid mask is a fort).**

$$\forall m \in \mathrm{Nat},\; \operatorname{fortOK}\left(m\right) = \mathrm{true} \Rightarrow \operatorname{IsFort}\left(\operatorname{gp}\left(13, 3\right), \operatorname{maskSet13}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.fortOK_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The fort predicate guarantees a nonempty decoded set with no unique outside neighbor.

**Definition 1.6 (Encode a finite vertex set).**

$$\forall S \in \operatorname{Finset}\left(\mathrm{V13}\right),\; \operatorname{setMask13}\left(S\right) = \sum _{v \in S}2^{\operatorname{code13}\left(v\right)}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.setMask13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The mask of a set is the sum of the powers of two at its vertex positions.

**Theorem 1.7 (Membership is recovered bit by bit).**

$$\forall S \in \operatorname{Finset}\left(\mathrm{V13}\right),\; \forall v \in \mathrm{V13},\; \operatorname{testBit}\left(\operatorname{setMask13}\left(S\right), \operatorname{code13}\left(v\right)\right) = \mathrm{true} \Leftrightarrow v \in S$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.testBit_setMask13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Encoding a finite set recovers exactly its membership bits.

**Theorem 1.8 (Every set mask fits in twenty-six bits).**

$$\forall S \in \operatorname{Finset}\left(\mathrm{V13}\right),\; \operatorname{setMask13}\left(S\right) < 2^{26}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.setMask13_lt_two_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

No vertex position reaches twenty-six, so the encoded mask is below two to the twenty-sixth power.

**Definition 1.9 (Rotate all selected vertices).**

$$\forall r \in \operatorname{Fin}\left(13\right),\; \forall S \in \operatorname{Finset}\left(\mathrm{V13}\right),\; \operatorname{rotateFinset13}\left(r, S\right) = \left\{\operatorname{rotate13}\left(r, v\right) \mid v \in S\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.rotateFinset13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Apply the same column rotation to every vertex of the finite set.

**Theorem 1.10 (Every oriented edge has an anchor).**

$$\forall u \in \mathrm{V13},\; \forall w \in \mathrm{V13},\; \operatorname{Adj}\left(\operatorname{gp}\left(13, 3\right), u, w\right) \Rightarrow \left(\exists a \in \mathrm{Anchor13},\; \operatorname{anchorTarget}\left(a\right) = \operatorname{rotate13}\left(\operatorname{snd}\left(u\right), w\right) \land \operatorname{anchorRequired}\left(a\right) = \operatorname{insert}\left(\operatorname{rotate13}\left(\operatorname{snd}\left(u\right), u\right), \left\{\operatorname{rotate13}\left(\operatorname{snd}\left(u\right), v\right) \mid v \in \operatorname{erase}\left(\operatorname{neighbors13}\left(u\right), w\right)\right\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.initialForce_anchor13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Rotate the source of an oriented edge to column zero. One of the six anchors has the rotated target and the rotated source together with its other two neighbors.

**Theorem 1.11 (An ordered family contains every candidate).**

$$\forall a \in \mathrm{Anchor13},\; \forall rows \in \operatorname{List}\left(\mathrm{Nat}\times \mathrm{Nat}\right),\; \forall m \in \mathrm{Nat},\; \left(\operatorname{familyOrderOK}\left(rows\right) = \mathrm{true} \land \left(\left(\forall row \in \mathrm{Nat}\times \mathrm{Nat},\; row \in rows \Rightarrow \operatorname{candidateShapeOK}\left(a, \operatorname{fst}\left(row\right)\right) = \mathrm{true}\right) \land \operatorname{candidateShapeOK}\left(a, m\right) = \mathrm{true}\right)\right) \Rightarrow \left(\exists f \in \mathrm{Nat},\; (m, f) \in rows\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.orderedRows_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A family of 7315 strictly increasing keys, all of the chosen anchor shape, contains every mask with that shape.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.IsFort`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.bitCount26_eq_card_maskSet13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.finiteNeighbors`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.fortOK_sound`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.initialForce_anchor13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.neighbors13_spec`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.orderedRows_complete`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.rotateFinset13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.setMask13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.setMask13_lt_two_pow`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.testBit_setMask13`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation](ParityRefutation.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore](ZeroForcingThreeFiniteCore.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation](ZeroForcingThreeFiniteRotation.md)
