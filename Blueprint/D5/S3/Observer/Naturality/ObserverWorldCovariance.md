# Observer World Covariance

## Abstract

Covariant observers on transitive axes have equivalent output worlds.

**Theorem 1.1 (Any two observer worlds are equivalent).**

$$\begin{aligned}\forall G, A, X, Y: \operatorname{Type},\\{}[\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, A\right)], [\operatorname{MulAction}\left(G, X\right)],\\{}[\operatorname{IsPretransitive}\left(G, A\right)],\\{}\forall O: A \to \left(X \to Y\right), U: G \to \operatorname{Equiv}\left(Y, Y\right),\\{}(\forall g: G, a: A, x: X, \operatorname{apply}\left(O, \operatorname{smul}\left(g, a\right), \operatorname{smul}\left(g, x\right)\right) = \operatorname{apply}\left(U, g, \operatorname{apply}\left(O, a, x\right)\right)) \Rightarrow\\{}\forall a: A, b: A,\\{}\exists g: G, \exists T: \operatorname{Equiv}\left(\operatorname{range}\left(\operatorname{apply}\left(O, a\right)\right), \operatorname{range}\left(\operatorname{apply}\left(O, b\right)\right)\right),\\{}\operatorname{smul}\left(g, a\right) = b \land (\forall x: X, \operatorname{apply}\left(T, \operatorname{apply}\left(O, a, x\right)\right) = \operatorname{apply}\left(U, g, \operatorname{apply}\left(O, a, x\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/ObserverWorldCovariance.observer_world_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observer world is constructed directly as the range of that axis's state-to-output map. Transitivity supplies a group element carrying one axis to the other.

Covariance shows that the corresponding output equivalence maps the first range onto the second. Restricting it to these ranges produces the displayed equivalence and transition computation rule.

Repository and pinned-library searches found no complete observer-world result. The generic transitivity witness and subtype restriction construction are applied directly.

## References

- Truth anchor: `D5/S3/Observer/Naturality/ObserverWorldCovariance.observer_world_covariance`
