# Binary Character Profile Rank Cardinality

## Abstract

The binary-character span rank determines the realized profile count and every realized fiber size.

**Theorem 1.1 (Character rank controls profiles and fibers).**

$$\begin{gathered}\forall G, I: \operatorname{Type},\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Fintype}(G)], [\operatorname{Fintype}(I)],\\{}chi: I \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}\operatorname{let}(Phi(g)(c) := chi(c)(\operatorname{mkQ}(2, g)), H := \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)), r := \operatorname{finrank}(\operatorname{ZMod}(2), H))\;\\{}\operatorname{ker}(Phi) = \operatorname{iInf}(c, I, \operatorname{ker}(chi(c) \circ \operatorname{mkQ}(2))), \operatorname{card}(\operatorname{range}(Phi)) = 2^{r}, \forall b: \operatorname{range}(Phi), \operatorname{card}({\{g: G \mid Phi(g) = b\}}) = \frac{\operatorname{card}(G)}{2^{r}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality.binary_character_profile_rank_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group is finite abelian. Each binary character is a linear functional on the canonical quotient by doubles and is evaluated back on the original group.

The joint profile is constructed componentwise from those characters. Its rank is the finite dimension of their linear span.

All three conclusions are public: the kernel intersection, the power-of-two realized image count, and the uniform cardinality of every realized profile fiber.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality.binary_character_profile_rank_cardinality`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Fourier/BinaryCharacterBasisMinimality](../BinaryCharacterBasisMinimality.md)
