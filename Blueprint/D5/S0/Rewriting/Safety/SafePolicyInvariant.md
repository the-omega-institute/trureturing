# Safe Policy Invariance

## Abstract

A policy selecting only controls whose possible responses stay in the safe kernel preserves the kernel and safety.

**Theorem 1.1 (Safe policies preserve the safe kernel).**

$$\begin{gathered}K^* \subseteq S,\\{}U_{safe}(x) := \{u \in U(x) \mid \forall y, \operatorname{R}\left(x, u, y\right) \Rightarrow y \in K^*\},\\{}\forall x, pi(x) \in U_{safe}(x)\\{}\Rightarrow \forall x_{0}, x_{t}, x_{0} \in K^* \land \operatorname{Reachable}\left(\operatorname{PolicyStep}\left(R, pi\right), x_{0}, x_{t}\right)\\{}\Rightarrow x_{t} \in K^* \land x_{t} \in S.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Safety/SafePolicyInvariant.safe_policy_preserves_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each state, the safe-control set is constructed from the available controls and the response relation: every possible successor must lie in the safe kernel.

The policy-induced transition relation is passed directly to the canonical invariant-safety theorem. Every finitely reachable state therefore lies in the kernel and, by inclusion, in S.

## References

- Truth anchor: `D5/S0/Rewriting/Safety/SafePolicyInvariant.safe_policy_preserves_kernel`
- Dependency: [D5/S0/Rewriting/Safety/InvariantSafety](InvariantSafety.md)
