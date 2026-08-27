# Continuous Local Factor Gluing

## Abstract

Compatible continuous local factors glue uniquely and factor the target globally.

**Theorem 1.1 (Continuous local factors glue uniquely).**

$$\forall I \in \operatorname{Type}\left(\right), X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), q \in X \to B, T \in X \to Y, U \in I \to \left(B \to \operatorname{Prop}\left(\right)\right), f \in \forall i: I, \operatorname{ContinuousMap}\left(\operatorname{Subtype}\left(U\left(i\right)\right), Y\right),\; \left(\left(\operatorname{TopologicalSpace}\left(B\right) \land \operatorname{TopologicalSpace}\left(Y\right)\right) \land \left(\left(\forall i \in I,\; \operatorname{IsOpen}\left(U\left(i\right)\right)\right) \land \left(\operatorname{iUnion}\left(U\right) = \operatorname{univ}\left(B\right) \land \left(\operatorname{Surjective}\left(q\right) \land \left(\forall i \in I, x \in X,\; \operatorname{mem}\left(q\left(x\right), U\left(i\right)\right) \Rightarrow T\left(x\right) = \operatorname{localApply}\left(f, i, q\left(x\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in I, j \in I, b \in B,\; \left(\operatorname{mem}\left(b, U\left(i\right)\right) \land \operatorname{mem}\left(b, U\left(j\right)\right)\right) \Rightarrow \operatorname{localApply}\left(f, i, b\right) = \operatorname{localApply}\left(f, j, b\right)\right) \land \exists! g: \operatorname{ContinuousMap}\left(B, Y\right), \left(\forall i \in I, b \in B,\; \operatorname{mem}\left(b, U\left(i\right)\right) \Rightarrow g\left(b\right) = \operatorname{localApply}\left(f, i, b\right)\right) \land T = \operatorname{compose}\left(g, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing.continuous_local_factors_glue_uniquely` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local factors are continuous maps on the exact cover subtypes. Surjectivity and the shared target factorization invoke the frozen overlap theorem, giving equality on every pairwise intersection.

The domains are publicly open and cover the base. Mathlib's canonical continuous-map lift therefore glues the local maps, and its computation rule states that the global map restricts to each local factor.

Cover membership proves uniqueness pointwise. Applying the same local computation rule at q(x), together with the supplied local factorization equation, proves the public identity T = f composed with q.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing.continuous_local_factors_glue_uniquely`
- Dependency: [D5/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility](LocalFactorOverlapCompatibility.md)
