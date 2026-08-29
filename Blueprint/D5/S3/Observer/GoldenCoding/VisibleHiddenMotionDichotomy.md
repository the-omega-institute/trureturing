# Visible Paths and Hidden Address Jumps

## Abstract

Continuous solenoid histories remain on visible flow lines, whereas a canonical hidden integer action has no continuous real extension.

**Theorem 1.1 (Continuity is carried by flow lines and hidden changes are rigid).**

$$\begin{aligned}(\forall x, y: UniversalSolenoid, \operatorname{Joined}\left(x, y\right) \iff \exists t: \mathbb{R}, y = \operatorname{realFlow}\left(t\right) + x) \land\\(\forall segment: \operatorname{Set}\left(\mathbb{R}\right), \operatorname{IsPreconnected}\left(segment\right) \Rightarrow \forall offset: \mathbb{R} \to HiddenAddress, \operatorname{ContinuousOn}\left(offset, segment\right) \Rightarrow \forall first, second: \mathbb{R}, first \in segment \land second \in segment \Rightarrow offset\left(first\right) = offset\left(second\right)) \land\\discreteHiddenJump \neq 0 \land \neg \exists flow: \operatorname{CAddHom}\left(\mathbb{R}, HiddenAddress\right), flow \circ cast_{\mathbb{Z}} = discreteHiddenJump.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy.visible_path_hidden_address_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen path-orbit theorem identifies continuous reachability in the universal solenoid with translation along one real-flow orbit. The frozen hidden-fiber theorem independently makes every continuous hidden-address map on a preconnected real segment constant.

The same public statement names the canonical additive integer jump. It is nonzero, and frozen continuous rigidity rules out any continuous additive real flow whose restriction along integer casting is that jump. Thus the discrete witness and its obstruction concern one map.

No new motion, address, path, or flow object is introduced here. Each clause uses the canonical carrier and operation from its frozen owner.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy.visible_path_hidden_address_dichotomy`
- Dependency: [D5/S1/Solenoid/PathOrbitClassification](../../../S1/Solenoid/PathOrbitClassification.md)
- Dependency: [D5/S3/Observer/HiddenFlow/DiscreteRigidity](../HiddenFlow/DiscreteRigidity.md)
