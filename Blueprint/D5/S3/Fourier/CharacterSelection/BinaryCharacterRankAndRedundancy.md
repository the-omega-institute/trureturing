# Binary Character Rank And Redundancy

## Abstract

Binary-character span rank counts independent joint outputs and identifies redundant roles.

**Theorem 1.1 (Rank counts profiles and span dependence gives product recovery).**

$$\begin{gathered}\forall G, I: \operatorname{Type},\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Fintype}(G)], [\operatorname{Fintype}(I)],\\{}chi: I \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}\operatorname{let}(Phi(g) := {chi(i)(\operatorname{mkQ}(2, g))_{i \in I}}, H := \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)), r := \operatorname{finrank}(\operatorname{ZMod}(2), H))\;\\{}\operatorname{card}(\operatorname{range}(Phi)) = 2^{r} \land\\{}\forall j \in I, chi(j) \in \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(\operatorname{restrict}(chi, I \setminus \{j\}))) \Rightarrow \exists a: \operatorname{Finsupp}(I \setminus \{j\}, \operatorname{ZMod}(2)), \forall g \in G, \operatorname{ofAdd}(chi(j)(\operatorname{mkQ}(2, g))) = \prod_{i \in \operatorname{support}(a)} \operatorname{ofAdd}(a(i) \cdot chi(i)(\operatorname{mkQ}(2, g))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterRankAndRedundancy.binary_character_rank_and_redundancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each role is a binary linear character on the canonical quotient of a finite abelian group by doubles. Their joint profile is evaluated back on the original group.

The realized profile count is two raised to the finite dimension of the character span. A role lying in the span of all other roles has a finite coefficient witness whose multiplicative output is their product.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterRankAndRedundancy.binary_character_rank_and_redundancy`
- Dependency: [D5/S3/Fourier/BinaryCharacterRedundancyCriterion](../BinaryCharacterRedundancyCriterion.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality](BinaryCharacterProfileRankCardinality.md)
