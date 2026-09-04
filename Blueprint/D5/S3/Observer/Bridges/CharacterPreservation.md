# Reflection Character Preservation

## Abstract

An equivariant real-linear bridge preserves both reflection characters and has no nonzero response of the opposite character.

**Theorem 1.1 (Equivariant bridges preserve reflection characters).**

$$\begin{aligned}\forall C, Z: \operatorname{Type},\\{}[\operatorname{AddCommGroup}\left(C\right)], [\operatorname{Module}\left(\mathbb{R}, C\right)], [\operatorname{AddCommGroup}\left(Z\right)], [\operatorname{Module}\left(\mathbb{R}, Z\right)],\\{}configReflection: \operatorname{LinearMap}\left(\mathbb{R}, C, C\right), responseReflection: \operatorname{LinearMap}\left(\mathbb{R}, Z, Z\right), bridge: \operatorname{LinearMap}\left(\mathbb{R}, C, Z\right),\\{}Function.Semiconj\left(bridge, configReflection, responseReflection\right) \Rightarrow\\{}(\forall x \in C,\; \operatorname{apply}\left(configReflection, x\right) = x \Rightarrow \operatorname{apply}\left(responseReflection, \operatorname{apply}\left(bridge, x\right)\right) = \operatorname{apply}\left(bridge, x\right)) \land\\{}(\forall x \in C,\; \operatorname{apply}\left(configReflection, x\right) = -x \Rightarrow \operatorname{apply}\left(responseReflection, \operatorname{apply}\left(bridge, x\right)\right) = -\operatorname{apply}\left(bridge, x\right)) \land\\{}(\forall x \in C,\; \operatorname{apply}\left(configReflection, x\right) = x \Rightarrow \left(\operatorname{apply}\left(responseReflection, \operatorname{apply}\left(bridge, x\right)\right) = -\operatorname{apply}\left(bridge, x\right) \Rightarrow \operatorname{apply}\left(bridge, x\right) = 0\right)) \land\\{}(\forall x \in C,\; \operatorname{apply}\left(configReflection, x\right) = -x \Rightarrow \left(\operatorname{apply}\left(responseReflection, \operatorname{apply}\left(bridge, x\right)\right) = \operatorname{apply}\left(bridge, x\right) \Rightarrow \operatorname{apply}\left(bridge, x\right) = 0\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/CharacterPreservation.character_preservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the configuration and response carriers be real modules. The two linear reflections act on their respective carriers, and the linear bridge intertwines those actions.

Fixed configurations map to fixed responses, while negated configurations map to negated responses. A response lying in the opposite character sector is therefore zero.

## References

- Truth anchor: `D5/S3/Observer/Bridges/CharacterPreservation.character_preservation`
- Dependency: [D5/S3/Observer/Bridges/FixedPointSemiconjugacy](FixedPointSemiconjugacy.md)
