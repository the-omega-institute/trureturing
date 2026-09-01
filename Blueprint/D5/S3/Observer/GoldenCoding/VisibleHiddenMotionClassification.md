# Universal-Solenoid Visible-Hidden Motion Classification

## Abstract

The universal solenoid is connected but not path-connected, and every continuous history has one visible lift and one constant hidden offset. Distinct hidden addresses instead determine nonzero discrete jumps with no continuous real extension.

**Theorem 1.1 (Visible phase paths and hidden address jumps are exhaustive).**

$$\begin{gathered}(\operatorname{ConnectedSpace}\left(UniversalSolenoid\right) \land \neg \operatorname{PathConnectedSpace}\left(UniversalSolenoid\right)) \land\\{}(\forall x, y: UniversalSolenoid, \operatorname{Joined}\left(x, y\right) \iff \exists t: \mathbb{R}, y = \operatorname{realFlow}\left(t\right) + x) \land\\{}(\forall \gamma: \operatorname{C}\left(\mathbb{R}, UniversalSolenoid\right), \exists! data: \operatorname{C}\left(\mathbb{R}, \mathbb{R}\right) \times \ker(projection), \operatorname{fst}\left(data\right)\left(0\right) = \operatorname{baseRepresentative}\left(\gamma, 0\right) \land \forall t: \mathbb{R}, \gamma\left(t\right) = \operatorname{realFlow}\left(\operatorname{fst}\left(data\right)\left(t\right)\right) + \operatorname{snd}\left(data\right)) \land\\{}(\forall first, second: HiddenAddress, first \neq second \Rightarrow ((\neg \exists motion: unitInterval \to HiddenAddress, \operatorname{Continuous}\left(motion\right) \land motion\left(0\right) = first \land motion\left(1\right) = second) \land (\exists jump: \operatorname{AddHom}\left(\mathbb{Z}, HiddenAddress\right), jump\left(1\right) = second - first \land jump \neq 0 \land \neg \exists flow: \operatorname{CAddHom}\left(\mathbb{R}, HiddenAddress\right), \operatorname{comp}\left(\operatorname{toAddMonoidHom}\left(flow\right), \operatorname{castAddHom}\left(\mathbb{Z}, \mathbb{R}\right)\right) = jump))) \land\\{}(\forall jump: \operatorname{AddHom}\left(\mathbb{Z}, HiddenAddress\right), jump \neq 0 \Rightarrow \neg \exists flow: \operatorname{CAddHom}\left(\mathbb{R}, HiddenAddress\right), \operatorname{comp}\left(\operatorname{toAddMonoidHom}\left(flow\right), \operatorname{castAddHom}\left(\mathbb{Z}, \mathbb{R}\right)\right) = jump).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/VisibleHiddenMotionClassification.universal_solenoid_visible_hidden_motion_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal solenoid is connected, but an explicit hidden-kernel point lies outside the real-flow orbit of zero. The frozen path-orbit classification therefore supplies both non-path-connectedness and the exact path-reachable set of every point.

Every continuous solenoid path has a unique real lift normalized at time zero and one constant element of the visible projection kernel. This is the whole-solenoid phase branch of the classification.

For any two distinct hidden addresses, no continuous unit-interval hidden motion joins them. Their difference canonically generates a nonzero integer-parameter additive action, and continuous hidden-flow rigidity prevents that action, or any nonzero integer action, from extending to a continuous additive real flow.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/VisibleHiddenMotionClassification.universal_solenoid_visible_hidden_motion_classification`
- Dependency: [D5/S1/Solenoid/HiddenMotionRigidity](../../../S1/Solenoid/HiddenMotionRigidity.md)
- Dependency: [D5/S1/Solenoid/StreamlineDecomposition](../../../S1/Solenoid/StreamlineDecomposition.md)
- Dependency: [D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy](VisibleHiddenMotionDichotomy.md)
- Dependency: [D5/S3/Observer/HiddenFlow/DiscreteRigidity](../HiddenFlow/DiscreteRigidity.md)
- Dependency: [D5/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation](../HiddenFlow/NormalizedHiddenAddressConservation.md)
- Dependency: [D5/S3/Observer/MetricGeometryLaws/HiddenTranslationComponentCharge](../MetricGeometryLaws/HiddenTranslationComponentCharge.md)
