# Invariant octic rank rigidity

## Abstract

The rank arguments consumed by the actual octic window theorem.

All statements concern finite coordinate labels over an arbitrary field. Group actions are finite and literal. toMatrix is the standard coordinate matrix; block uses the indicated row and column subtypes. These symbolic dimension and orbit arguments are not a finite certified instance or enumeration. The source is the rank and cut argument of general section 43.2, together with the strict-rank mechanism of section 26. No mathematical novelty is claimed.

**Theorem 1.1 (Complementary coordinate images are disjoint).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall S \in \operatorname{Finset}\left(Omega\right),\; \operatorname{Disjoint}\left(\operatorname{projected}\left(U, S\right), \operatorname{projected}\left(U, \operatorname{compl}\left(S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.projected_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

projected(U,S) is the image of U under the coordinate projection retaining S. The two images have disjoint coordinate supports. This gives one of the two dimension identities used in window connectivity.

**Theorem 1.2 (The window lies in the sum of its projected images).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall S \in \operatorname{Finset}\left(Omega\right),\; U \subseteq \operatorname{sup}\left(\operatorname{projected}\left(U, S\right), \operatorname{projected}\left(U, \operatorname{compl}\left(S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.window_le_projected_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector is the sum of its two complementary coordinate projections. Together with complementary disjointness, this bounds the window dimension by the sum of the projection dimensions.

**Theorem 1.3 (Complementary rank equality forces projection stability).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall S \in \operatorname{Finset}\left(Omega\right),\; (\operatorname{rowRank}\left(U, S\right) + \operatorname{rowRank}\left(U, \operatorname{compl}\left(S\right)\right) = \operatorname{finrank}\left(K, U\right)) \Rightarrow (\forall x \in \operatorname{Map}\left(Omega, K\right),\; (x \in U) \Rightarrow (\operatorname{coordinateProject}\left(S, x\right) \in U))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.projection_stable_of_rank_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rowRank(U,S) is the dimension of projected(U,S). Equality in the complementary dimension bound makes U equal the direct sum of those images. Its S projection therefore preserves U. The actual scalar-idealizer argument uses this conclusion to exclude equality.

**Theorem 1.4 (Membership in an actual translate).**

$$\forall Omega \in Type,\; \forall G \in Type,\; [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{MulAction}\left(G, Omega\right)] \forall S \in \operatorname{Finset}\left(Omega\right),\; \forall g \in G,\; \forall i \in Omega,\; (i \in \operatorname{orbitSet}\left(S, g\right)) \Leftrightarrow (\operatorname{act}\left(\operatorname{inverse}\left(g\right), i\right) \in S)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.mem_orbitSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

orbitSet(S,g) is the image of S under the action of g. This identity connects the Galois semilinear coordinate map to the translated projection.

**Theorem 1.5 (Connected transitive half-ranks are strictly balanced).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall G \in Type,\; [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{MulAction}\left(G, Omega\right)] ((\operatorname{card}\left(Omega\right) = 8) \land ((\operatorname{finrank}\left(K, U\right) = 4) \land ((\forall x \in Omega,\; \forall y \in Omega,\; \exists g \in G,\; \operatorname{act}\left(g, x\right) = y) \land ((\forall g \in G,\; \forall T \in \operatorname{Finset}\left(Omega\right),\; \operatorname{rowRank}\left(U, \operatorname{orbitSet}\left(T, g\right)\right) = \operatorname{rowRank}\left(U, T\right)) \land (\forall T \in \operatorname{Finset}\left(Omega\right),\; ((\operatorname{Nonempty}\left(T\right)) \land (\operatorname{Nonempty}\left(\operatorname{compl}\left(T\right)\right))) \Rightarrow (4 < \operatorname{rowRank}\left(U, T\right) + \operatorname{rowRank}\left(U, \operatorname{compl}\left(T\right)\right))))))) \Rightarrow (\forall S \in \operatorname{Finset}\left(Omega\right),\; ((\operatorname{Nonempty}\left(S\right)) \land (\operatorname{Nonempty}\left(\operatorname{compl}\left(S\right)\right))) \Rightarrow (\operatorname{card}\left(S\right) + 1 \le 2 \cdot \operatorname{rowRank}\left(U, S\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.invariant_half_rank_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fractional_submodular_cover theorem is applied to translates of S with their constant covering multiplicity to obtain the weak half-rank bound. For the nonnegative invariant submodular defect 2 rowRank minus cardinality, a minimal nonempty zero set has translates that cannot cross any zero set. Transitivity covers the complement by such translates, so equality on S forces equality on its complement. Connectedness excludes both equalities. This equality-rigidity argument supplies the strict-rank bound for the actual split window.

**Theorem 1.6 (Operator crossing rank equals its literal matrix block rank).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall n \in \operatorname{LinearMap}\left(K, \operatorname{Map}\left(Omega, K\right), \operatorname{Map}\left(Omega, K\right)\right),\; \forall S \in \operatorname{Finset}\left(Omega\right),\; \operatorname{rank}\left(\operatorname{block}\left(\operatorname{toMatrix}\left(n\right), S, \operatorname{compl}\left(S\right)\right)\right) = \operatorname{crossRank}\left(n, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.crossRank_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

crossRank(n,S) is the dimension of the image of extension by zero from S complement, followed by n and projection to S. The literal subtype-indexed matrix block represents that map; extension by zero in the target is injective. The actual cut-free endpoint uses this identity to state its conclusion using the actual matrix entries.

**Theorem 1.7 (Crossing rank bounds the projection dimension).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall n \in \operatorname{LinearMap}\left(K, \operatorname{Map}\left(Omega, K\right), \operatorname{Map}\left(Omega, K\right)\right),\; \forall S \in \operatorname{Finset}\left(Omega\right),\; ((\operatorname{ker}\left(n\right) = U) \land ((\operatorname{range}\left(n\right) = U) \land ((\operatorname{card}\left(Omega\right) = 8) \land (\operatorname{finrank}\left(K, U\right) = 4)))) \Rightarrow (2 \cdot \operatorname{rowRank}\left(U, S\right) \le \operatorname{card}\left(S\right) + \operatorname{crossRank}\left(n, S\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.cross_rank_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rank-nullity for extension from the complementary coordinates, followed by n and projection to S, gives this bound whenever n has kernel and image U. Together with strict projection ranks it forces every nontrivial directed crossing block to be nonzero.

**Theorem 1.8 (Transitive strict half-ranks exclude a cut on eight labels).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] \forall U \in \operatorname{Submodule}\left(K, \operatorname{Map}\left(Omega, K\right)\right),\; \forall G \in Type,\; [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{MulAction}\left(G, Omega\right)] \forall n \in \operatorname{LinearMap}\left(K, \operatorname{Map}\left(Omega, K\right), \operatorname{Map}\left(Omega, K\right)\right),\; ((\operatorname{ker}\left(n\right) = U) \land ((\operatorname{range}\left(n\right) = U) \land ((\operatorname{card}\left(Omega\right) = 8) \land ((\operatorname{finrank}\left(K, U\right) = 4) \land ((\forall x \in Omega,\; \forall y \in Omega,\; \exists g \in G,\; \operatorname{act}\left(g, x\right) = y) \land ((\forall g \in G,\; \forall T \in \operatorname{Finset}\left(Omega\right),\; \operatorname{rowRank}\left(U, \operatorname{orbitSet}\left(T, g\right)\right) = \operatorname{rowRank}\left(U, T\right)) \land (\forall T \in \operatorname{Finset}\left(Omega\right),\; ((0 < \operatorname{card}\left(T\right)) \land (\operatorname{card}\left(T\right) < 8)) \Rightarrow (\operatorname{card}\left(T\right) + 1 \le 2 \cdot \operatorname{rowRank}\left(U, T\right))))))))) \Rightarrow (\forall S \in \operatorname{Finset}\left(Omega\right),\; ((2 \le \operatorname{card}\left(S\right)) \land (\operatorname{card}\left(S\right) \le 6)) \Rightarrow ((2 \le \operatorname{crossRank}\left(n, S\right)) \lor (2 \le \operatorname{crossRank}\left(n, \operatorname{compl}\left(S\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricOcticRanks.cut_free_of_actual_ranks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rank-nullity bounds 2 rowRank(U,S) by card(S) plus crossRank(n,S). If both crossing ranks were at most one for a cut of size two through six, the strict lower bounds force a three-element side of rank two with complement of rank three. Submodularity and strict rank imply that two translates of this triple are equal or disjoint, using the complement when the intersection has one element. Transitivity then partitions eight labels into triples, which is impossible. The actual-window theorem supplies every premise from its original window; it does not assume this rank model as additional data.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.crossRank_matrix`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.cross_rank_bound`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.cut_free_of_actual_ranks`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.invariant_half_rank_strict`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.mem_orbitSet`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.projected_disjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.projection_stable_of_rank_equality`
- Truth anchor: `D5/S3/Quantum/Algebra/AuricOcticRanks.window_le_projected_sup`
- Dependency: [D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses](../../Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.md)
