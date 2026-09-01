# Compact Character Modulus and Mellin Obstruction

## Abstract

Continuous complex characters on compact groups have unit modulus, so a Mellin mode with nonzero real drift cannot descend through a Pontryagin character.

**Theorem 1.1 (Compact characters exclude nonzero Mellin drift).**

$$\begin{gathered}\forall G,\\{}\operatorname{Group}(G) \land \operatorname{TopologicalSpace}(G) \land \operatorname{IsTopologicalGroup}(G) \land \operatorname{CompactSpace}(G) \Rightarrow\\{}(\forall chi: \operatorname{ContinuousMonoidHom}(G, \operatorname{Units}(\mathbb{C})), \forall g \in G, \left\lVert \operatorname{coe}(\operatorname{chi}(g)) \right\rVert = 1) \land\\{}(\forall \delta, \gamma \in \mathbb{R}, \delta \neq 0 \Rightarrow\\{}\forall descent: \operatorname{ContinuousMonoidHom}(\operatorname{Multiplicative}(\mathbb{R}), G), phase: \operatorname{PontryaginDual}(G), \neg \forall t \in \mathbb{R}, \operatorname{mellinCharacter}(\operatorname{coe}(\delta) + i \cdot \operatorname{coe}(\gamma), \operatorname{ofAdd}(t)) = \operatorname{coe}(\operatorname{phase}(\operatorname{descent}(\operatorname{ofAdd}(t))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/CompactCharacterMellinObstruction.compact_character_modulus_and_mellin_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier G is an arbitrary compact topological group. A continuous homomorphism from G to the units of the complex numbers is bounded on its compact source; applying the same bound to every positive power and to the inverse forces unit norm.

The second public conjunct uses the canonical repository Mellin character. If it factored through a Pontryagin character, every value would lie on the complex unit circle, contradicting the exact frozen criterion when the real drift delta is nonzero.

The no-factorization statement quantifies the descent map, phase character, drift, frequency, and time; it does not replace the source character by an abstract unitary predicate.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/CompactCharacterMellinObstruction.compact_character_modulus_and_mellin_obstruction`
- Dependency: [D5/S3/Weil/ZetaLinear/OfflineZeroCharacter](OfflineZeroCharacter.md)
