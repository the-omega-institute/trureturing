# Toroidal Jet Depth

## Abstract

The first derivative layer visible to some normalized toroidal period equals the natural vanishing multiplicity of xi.

**Theorem 1.1 (Toroidal jet depth equals xi multiplicity).**

$$\forall Index \in \operatorname{Type}\left(\right), s \in \operatorname{Complex}\left(\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index,\; \operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), T\left(i\right)\right)\right) \land \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right) \Rightarrow \operatorname{sInf}\left(\{j \in \operatorname{Nat}\left(\right) \mid \exists i \in Index,\; \operatorname{iteratedDeriv}\left(j, xiReading \times T\left(i\right), s\right) \ne 0\}\right) = \operatorname{analyticOrderNatAt}\left(xiReading, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalJetDepth.toroidal_jet_depth_eq_vanishing_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The depth is exposed directly as the natural infimum of indices at which some normalized xi-times-twist period has a nonzero iterated derivative.

The canonical nonzero endpoint value of xi rules out infinite local order. Mathlib then identifies its natural analytic order with the first nonzero derivative layer.

Every twist product has order at least the xi order, while the twist that is nonzero at the observation point realizes equality. Thus the same layer is first visible across the toroidal family.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalJetDepth.toroidal_jet_depth_eq_vanishing_order`
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](../../Zeros/Endpoints/XiEndpointValues.md)
