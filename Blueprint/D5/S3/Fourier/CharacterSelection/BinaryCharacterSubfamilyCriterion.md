# Binary Character Subfamily Criterion

## Abstract

A binary-character subfamily is sufficient exactly when it spans the full role space.

**Theorem 1.1 (Observation kernels, expressible targets, and character spans agree).**

$$\begin{gathered}\forall G, E, B,\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Finite}(G)],\\{}E, B: \operatorname{Set}(\operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2))),\\{}B \subseteq E \Rightarrow\\{}\operatorname{let}(profile(S)(g)(chi) := chi(\operatorname{mkQ}(2, g)), H := \operatorname{span}(\operatorname{ZMod}(2), E))\;\\{}\operatorname{ListTFAE}({[\operatorname{ker}(profile(B)) = \operatorname{ker}(profile(E)), \forall Y: \operatorname{Type}, \{K: G \to Y \mid \operatorname{Refines}(K, \operatorname{effectiveReadout}(profile(B)))\} = \{K: G \to Y \mid \operatorname{Refines}(K, \operatorname{effectiveReadout}(profile(E)))\}, \operatorname{span}(\operatorname{ZMod}(2), B) = H]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterSubfamilyCriterion.binary_character_subfamily_sufficiency_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a set of binary characters on a finite abelian group and let B be a subset. Each character is evaluated on the original group through the canonical quotient by doubles.

The displayed profile is the canonical joint readout of a character set. Expressibility uses its canonical effective-image readout and the repository refinement relation.

The public three-way equivalence states equality of observation kernels, equality of expressible target families for every target type, and equality of binary-character spans.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterSubfamilyCriterion.binary_character_subfamily_sufficiency_tfae`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality](../../ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Fourier/BinaryCharacterRedundancyCriterion](../BinaryCharacterRedundancyCriterion.md)
