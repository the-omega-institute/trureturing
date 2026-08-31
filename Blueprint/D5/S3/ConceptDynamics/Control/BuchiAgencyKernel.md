# Buchi Agency Kernel

## Abstract

The nested robust renewal kernel has a safe policy that renews infinitely often.

**Theorem 1.1 (Live agency is robustly safe and renews infinitely often).**

$$\forall G, L_{renew}, \operatorname{FiniteGame}\left(G\right) \Rightarrow\\{}\operatorname{LiveAgency}\left(G, L_{renew}\right) \subseteq \operatorname{FreeKernel}\left(G\right)_{rob} \land\\{}\exists r, pi, \operatorname{RankedRenewalPolicy}\left(G, \operatorname{LiveAgency}\left(G, L_{renew}\right), L_{renew}, r, pi\right) \land\\{}\forall x, (\operatorname{StartsIn}\left(x, \operatorname{LiveAgency}\left(G, L_{renew}\right)\right) \land \operatorname{Follows}\left(G, pi, x\right)) \Rightarrow\\{}(\forall t, \operatorname{At}\left(x, t\right) \in \operatorname{FreeKernel}\left(G\right)_{rob}) \land\\{}\forall N, \exists n, N \le n \land \operatorname{At}\left(x, n\right) \in L_{renew}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/BuchiAgencyKernel.live_agency_buchi_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inner regional attractor is the least fixed point of robust finite-horizon reachability. Finiteness supplies a natural-number arrival rank for every state in this attractor.

At the outer greatest fixed point, rank-positive states choose an action whose possible successors have smaller rank. Rank-zero states lie in the renewal set and choose an action back into the live kernel.

The resulting policy keeps every adversarial trajectory in LiveAgency, hence in the robust freedom kernel. Strict descent forces another renewal after every time bound, which is the Buchi condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/BuchiAgencyKernel.live_agency_buchi_kernel`
- Dependency: [D5/S3/ConceptDynamics/Control/FiniteHorizonReachability](FiniteHorizonReachability.md)
