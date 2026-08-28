# Self-Description Distance Classification

## Abstract

Self-description differences split into zero, finite-reachable, and horizon distances.

**Theorem 1.1 (Self-description differences have three operational distance classes).**

$$\begin{aligned}\forall I, S: Type, tau: \operatorname{Perm}\left(I\right),\\{}Delta: S \to I \to \mathbb{R}, \operatorname{let} D = \left\{\exists s: S, \operatorname{selfReadout}\left(Delta, s, \operatorname{fst}\left(p\right)\right) \neq \operatorname{selfReadout}\left(Delta, s, \operatorname{snd}\left(p\right)\right) \mid p \in I \times I\right\}\\{}\operatorname{in} (\forall p \in D, ((\operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) = 0 \land \forall f: I \to \mathbb{R}, \operatorname{edgeAdmissible}\left(tau, f\right) \Rightarrow f\left(\operatorname{fst}\left(p\right)\right) = f\left(\operatorname{snd}\left(p\right)\right)) \lor (0 < \operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) < \infty) \lor (\operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) = \infty \land \forall n: \mathbb{Z}, \operatorname{snd}\left(p\right) \neq \left(tau^{n}\right)\left(\operatorname{fst}\left(p\right)\right)))) \land\\{}((\forall p \in D, (\operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) = 0 \lor \operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) = \infty)) \Rightarrow \forall p \in D, \neg(\exists f: I \to \mathbb{R}, n: \mathbb{Z}, \operatorname{edgeAdmissible}\left(tau, f\right) \land f\left(\operatorname{fst}\left(p\right)\right) \neq f\left(\operatorname{snd}\left(p\right)\right) \land \operatorname{snd}\left(p\right) = \left(tau^{n}\right)\left(\operatorname{fst}\left(p\right)\right))) \land\\{}(\forall p \in D, (0 < \operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) < \infty) \Rightarrow \exists f: I \to \mathbb{R}, n: \mathbb{Z}, \operatorname{edgeAdmissible}\left(tau, f\right) \land f\left(\operatorname{fst}\left(p\right)\right) \neq f\left(\operatorname{snd}\left(p\right)\right) \land \operatorname{snd}\left(p\right) = \left(tau^{n}\right)\left(\operatorname{fst}\left(p\right)\right) \land \operatorname{observerDistance}\left(tau, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right) \leq \left|n\right|).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/SelfDescriptionDistanceClassification.self_description_distance_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A self-description difference is an endpoint pair separated by at least one member of the supplied self-readout family. The outside distance is the canonical supremum over bounded unit-edge readouts for the supplied permutation update.

Zero distance forces every admissible readout to agree. Infinite distance excludes every finite signed update path. If all self-description differences are in one of those two hidden classes, no admissible readout can distinguish a pair along such a path.

A finite-positive distance supplies both an admissible separating readout and a signed update path. The imported permutation-horizon theorem bounds the observer distance by that path's length.

## References

- Truth anchor: `D5/S3/ContinuousObservables/SelfDescriptionDistanceClassification.self_description_distance_classification`
- Dependency: [D5/S3/ContinuousObservables/PermutationOrbitHorizon](PermutationOrbitHorizon.md)
