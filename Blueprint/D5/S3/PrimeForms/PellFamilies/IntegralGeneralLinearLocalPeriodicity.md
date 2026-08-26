# Integral General-Linear Local Periodicity

## Abstract

Integral general-linear updates are permutations with pure-periodic prime-power reductions.

**Theorem 1.1 (Prime-power reductions of integral invertible updates are purely periodic).**

$$\begin{aligned}\forall d, p, k \in \mathbb{N},\\G: \operatorname{GL}\left(\operatorname{Fin}\left(d\right), \mathbb{Z}\right), \operatorname{Prime}\left(p\right) \Rightarrow\\\operatorname{let} q = p^{k}, Gq = \operatorname{mapEntries}\left(G, \operatorname{ZMod}\left(q\right)\right),\\tau = (v \mapsto \operatorname{mulVec}\left(Gq, v\right))\;\\\operatorname{Bijective}\left(tau\right) \land \forall x \in \operatorname{Vector}\left(\operatorname{ZMod}\left(q\right), d\right), \exists T \in \mathbb{N}, 0 < T \land \forall n \in \mathbb{N}, \operatorname{iterate}\left(tau, n + T, x\right) = \operatorname{iterate}\left(tau, n, x\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/IntegralGeneralLinearLocalPeriodicity.integral_general_linear_update_is_prime_power_pure_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local state carrier is the d-coordinate vector space over ZMod(p^k). The update is constructed by mapping the entries of the given integral general-linear matrix into that quotient and applying the resulting matrix to a local state.

General-linear base change preserves invertibility, so the displayed local update is bijective. On this finite carrier injectivity puts every initial state on a cycle, yielding a positive period whose periodicity law holds from time zero.

## References

- Truth anchor: `D5/S3/PrimeForms/PellFamilies/IntegralGeneralLinearLocalPeriodicity.integral_general_linear_update_is_prime_power_pure_periodic`
- Dependency: [D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity](LocalPellPeriodicity.md)
