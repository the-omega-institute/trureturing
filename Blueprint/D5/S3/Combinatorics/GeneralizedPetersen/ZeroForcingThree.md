# The Zero Forcing Number of P(n,3)

## Abstract

Eight vertices are necessary and sufficient to zero-force P(n,3) for every n at least thirteen.

**Definition 1.1 (Closure under the color-change rule).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \forall v \in V,\; \operatorname{Black}\left(G, S, v\right) \Leftrightarrow \left(\forall B \in \operatorname{Set}\left(V\right),\; \left(S \subseteq B \land \left(\forall u \in V,\; \forall w \in V,\; \left(u \in B \land \left(\operatorname{Adj}\left(G, u, w\right) \land \left(\forall x \in V,\; \left(\operatorname{Adj}\left(G, u, x\right) \land x \ne w\right) \Rightarrow x \in B\right)\right)\right) \Rightarrow w \in B\right)\right) \Rightarrow v \in B\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black` (`✓ std3`).

*Citation.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Black is the least set containing the initially black vertices S and closed under the color-change rule. A black source forces a neighboring vertex whenever all its other neighbors are black.

**Definition 1.2 (A zero forcing set).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \operatorname{IsZeroForcing}\left(G, S\right) \Leftrightarrow \left(\forall v \in V,\; \operatorname{Black}\left(G, S, v\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.IsZeroForcing` (`✓ std3`).

*Citation.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A set is zero forcing when its closure contains every vertex.

**Definition 1.3 (The minimum number of initial vertices).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{zeroForcingNumber}\left(G\right) = \operatorname{sInf}\left(\{ k \in \mathrm{Nat}| \exists S \in \operatorname{Finset}\left(V\right),\; \operatorname{card}\left(S\right) = k \land \operatorname{IsZeroForcing}\left(G, S\right)\} \right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.zeroForcingNumber` (`✓ std3`).

*Citation.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The zero forcing number is the infimum in the natural numbers of the cardinalities of finite zero forcing sets.

**Definition 1.4 (Krishnan Conjecture 5).**

$$\mathrm{claim} \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; 13 \le n \Rightarrow \operatorname{zeroForcingNumber}\left(\operatorname{gp}\left(n, 3\right)\right) = 8\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.claim` (`✓ std3`).

*Citation.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Conjecture 5 asserts that the zero forcing number of P(n,3) is eight for every natural n at least thirteen.

**Theorem 1.5 (Enlarging the initial black set).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \forall T \in \operatorname{Set}\left(V\right),\; \forall v \in V,\; \left(S \subseteq T \land \operatorname{Black}\left(G, S, v\right)\right) \Rightarrow \operatorname{Black}\left(G, T, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every forcing derivation from S remains valid after the initial set is enlarged to T.

**Theorem 1.6 (A first force inside a derivation).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \forall v \in V,\; \left(\operatorname{Black}\left(G, S, v\right) \land \left(\neg v \in S\right)\right) \Rightarrow \left(\exists u \in V,\; \exists w \in V,\; u \in S \land \left(\left(\neg w \in S\right) \land \left(\operatorname{Adj}\left(G, u, w\right) \land \left(\forall x \in V,\; \left(\operatorname{Adj}\left(G, u, x\right) \land x \ne w\right) \Rightarrow x \in S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.exists_initial_force` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A derivation reaching a vertex outside S contains an oriented edge whose source and all other neighbors are already in S, while its target is outside S.

**Theorem 1.7 (Transporting black vertices by an automorphism).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall e \in V\equiv V,\; \forall S \in \operatorname{Finset}\left(V\right),\; \forall v \in V,\; \left(\left(\forall x \in V,\; \forall y \in V,\; \operatorname{Adj}\left(G, \operatorname{e}\left(x\right), \operatorname{e}\left(y\right)\right) \Leftrightarrow \operatorname{Adj}\left(G, x, y\right)\right) \land \operatorname{Black}\left(G, S, v\right)\right) \Rightarrow \operatorname{Black}\left(G, \left\{\operatorname{e}\left(x\right) \mid x \in S\right\}, \operatorname{e}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.image_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An adjacency-preserving equivalence carries every forcing step to a forcing step from the image of the initial finite set.

**Theorem 1.8 (A disjoint fort remains white).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; \forall F \in \operatorname{Finset}\left(V\right),\; \forall v \in V,\; \left(\operatorname{Finite}\left(V\right) \land \left(\operatorname{IsFort}\left(G, F\right) \land \left(\operatorname{Disjoint}\left(S, F\right) \land v \in F\right)\right)\right) \Rightarrow \left(\neg \operatorname{Black}\left(G, S, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.not_black_of_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

If the initial set is disjoint from a fort, no vertex of the fort can become black.

**Theorem 1.9 (Substituting forcing derivations).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Set}\left(V\right),\; \forall T \in \operatorname{Set}\left(V\right),\; \forall v \in V,\; \left(\left(\forall x \in V,\; x \in T \Rightarrow \operatorname{Black}\left(G, S, x\right)\right) \land \operatorname{Black}\left(G, T, v\right)\right) \Rightarrow \operatorname{Black}\left(G, S, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.bind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

If every vertex of T can be forced from S, every vertex forced from T can also be forced from S.

**Theorem 1.10 (Eight consecutive outer vertices suffice).**

$$\forall n \in \mathrm{Nat},\; 9 \le n \Rightarrow \operatorname{IsZeroForcing}\left(\operatorname{gp}\left(n, 3\right), \left\{(\mathrm{false}, \operatorname{ofNat}\left(n, i\right)) \mid i \in \operatorname{range}\left(8\right)\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.outerBlock8_zeroForcing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For n at least nine, the outer vertices at columns zero through seven force all inner and outer vertices. The proof first forces inner vertices and extends the outer block, then propagates around the cycle.

**Definition 1.11 (External boundary of a finite graph).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall X \in \operatorname{Finset}\left(V\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \operatorname{externalBoundary}\left(G, X\right) = \{ v \in V| \left(\neg v \in X\right) \land \left(\exists u \in V,\; u \in X \land \operatorname{Adj}\left(G, u, v\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.externalBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The external boundary consists of vertices outside the selected set with at least one neighbor in it.

**Theorem 1.12 (The boundary of the first forcing sources).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; \forall p \in \mathrm{Nat},\; \left(\operatorname{Finite}\left(V\right) \land \left(\operatorname{IsZeroForcing}\left(G, S\right) \land \operatorname{card}\left(S\right) + p \le \operatorname{card}\left(V\right)\right)\right) \Rightarrow \left(\exists X \in \operatorname{Finset}\left(V\right),\; \operatorname{card}\left(X\right) = p \land \operatorname{card}\left(\operatorname{externalBoundary}\left(G, X\right)\right) \le \operatorname{card}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.firstForcers_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

If at least p forces are possible, there is a set of p distinct forcing sources whose external boundary has size at most the initial set.

**Theorem 1.13 (The thirteen-column case).**

$$\operatorname{zeroForcingNumber}\left(\operatorname{gp}\left(13, 3\right)\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.zeroForcingNumber13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The eight-vertex construction gives the upper bound. Every seven-vertex candidate with an initial force rotates into one of six anchor families, each containing a disjoint fort, which gives the lower bound.

**Theorem 1.14 (Eight for every circumference at least thirteen).**

$$\forall n \in \mathrm{Nat},\; 13 \le n \Rightarrow \operatorname{zeroForcingNumber}\left(\operatorname{gp}\left(n, 3\right)\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishnan-zero-forcing-generalized-petersen-three` (proved) by `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishnan-zero-forcing-generalized-petersen-three","declaration_gid":"D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For n at least fourteen, every ten-vertex set has external boundary at least eight. Applying the first-forcers inequality with ten sources excludes initial sets of at most seven vertices. The thirteen-column fort argument and the uniform eight-vertex construction complete the equality.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.IsZeroForcing`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.bind`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.claim`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.exists_initial_force`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.externalBoundary`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.firstForcers_boundary`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.image_equiv`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.mono`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.not_black_of_disjoint`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.outerBlock8_zeroForcing`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.zeroForcingNumber`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.zeroForcingNumber13`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary](ZeroForcingThreeBoundary.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite](ZeroForcingThreeFinite.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData1](ZeroForcingThreeFortData1.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData2](ZeroForcingThreeFortData2.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData3](ZeroForcingThreeFortData3.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData4](ZeroForcingThreeFortData4.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData5](ZeroForcingThreeFortData5.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFortData6](ZeroForcingThreeFortData6.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary](ZeroForcingThreeTenBoundary.md)
