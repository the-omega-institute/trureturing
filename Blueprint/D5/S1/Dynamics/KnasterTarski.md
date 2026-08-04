# Knaster-Tarski Extremal Fixed Points

## Abstract

Monotone endomorphisms have extremal fixed points, separated by a three-state cycle.

<a id="describe-least-and-greatest-fixed-points"></a>

**Theorem 1.1 (Least and greatest fixed points).**

$$f:L\to L\ \text{monotone}\Rightarrow \mu=\operatorname{lfp}(f)=\min\operatorname{Fix}(f),\ \nu=\operatorname{gfp}(f)=\max\operatorname{Fix}(f).$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/KnasterTarski.knaster_tarski_extremal_fixed_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classical Knaster-Tarski theorem states that every monotone endomorphism of a complete lattice has a least fixed point and a greatest fixed point. The Lean declaration is an honest repository wrapper around Mathlib's least and greatest fixed-point constructions and their extremality theorems. No repository literature note currently attests the classical source, so the provenance is conservatively recorded as repository-derived rather than literature-attested.

<a id="describe-three-state-successor-cycle"></a>

**Theorem 1.2 (Three-state successor cycle).**

$$F(X)=\{s\mid\operatorname{succ}(s)\in X\}\Rightarrow \operatorname{lfp}(F)=\varnothing,\ \operatorname{gfp}(F)=S.$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/KnasterTarski.three_cycle_extremal_fixed_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the three-state successor cycle, the induced powerset operator is inverse image under succession. It preserves the empty set and the full carrier; extremality therefore identifies the least fixed point with the empty set and the greatest fixed point with the full set. The inductive interpretation has no grounded state from which to begin, whereas the coinductive interpretation accepts the entire self-sustaining cycle.

## References

- Truth anchor: `D5/S1/Dynamics/KnasterTarski.knaster_tarski_extremal_fixed_points`
- Truth anchor: `D5/S1/Dynamics/KnasterTarski.three_cycle_extremal_fixed_points`
