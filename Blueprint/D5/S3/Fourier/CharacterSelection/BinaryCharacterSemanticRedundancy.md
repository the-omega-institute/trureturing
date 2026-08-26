# Binary Character Semantic Redundancy

## Abstract

Character-span rank separates semantic profile bits from dependent parity checks.

**Theorem 1.1 (Semantic information and transmission redundancy separate).**

$$\begin{gathered}\forall G, I: \operatorname{Type},\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Fintype}(G)], [\operatorname{Fintype}(I)],\\{}chi: I \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)), eta: \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}eta \in \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)) \Rightarrow\\{}\operatorname{let}(chiPlus: \operatorname{Option}(I) \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)), chiPlus(none) := eta, \forall i: I, chiPlus(some(i)) := chi(i),\\{}Phi(g)(i) := chi(i)(\operatorname{mkQ}(2, g)), PhiPlus(g)(j) := chiPlus(j)(\operatorname{mkQ}(2, g)),\\{}H := \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)), r := \operatorname{finrank}(\operatorname{ZMod}(2), H), R := \operatorname{ker}(\operatorname{linearCombination}(\operatorname{ZMod}(2), chi)),\\{}RPlus := \operatorname{ker}(\operatorname{linearCombination}(\operatorname{ZMod}(2), chiPlus)))\;\\{}\operatorname{card}(\operatorname{range}(Phi)) = 2^{r} \land\\{}\operatorname{finrank}(\operatorname{ZMod}(2), R) = \operatorname{card}(I) - r \land\\{}\operatorname{card}(\operatorname{range}(PhiPlus)) = \operatorname{card}(\operatorname{range}(Phi)) \land\\{}\operatorname{finrank}(\operatorname{ZMod}(2), RPlus) = \operatorname{finrank}(\operatorname{ZMod}(2), R) + 1 \land\\{}\exists a: \operatorname{Option}(I) \to \operatorname{ZMod}(2), a \in RPlus \land a(none) = 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterSemanticRedundancy.binary_character_semantic_redundancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Binary characters are linear functionals on the canonical quotient of a finite abelian group by doubles. Their joint profile and coefficient relation space are constructed from that family.

The character-span rank counts independent profile bits, while the kernel of coefficient synthesis counts role relations.

Adjoining a character already in the span preserves the realized profile count, adds one independent relation, and exposes a parity check with coefficient one on the new coordinate.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterSemanticRedundancy.binary_character_semantic_redundancy`
- Dependency: [D5/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality](BinaryCharacterProfileRankCardinality.md)
