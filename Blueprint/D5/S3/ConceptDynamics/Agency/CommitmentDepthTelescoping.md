# Commitment Depth Telescoping

## Abstract

Commitment depth is the finite telescoping loss of compatible future-plan capacity.

**Proposition 1.1 (Commitment depth telescopes along a finite history).**

$$\begin{aligned}\forall Plan: \operatorname{Type}, n: Nat,\\Omega: Nat \to \operatorname{Finset}(Plan),\\\sum_{t \in \operatorname{range}(n)} {\operatorname{log2}(\operatorname{card}(Omega(t))) - \operatorname{log2}(\operatorname{card}(Omega(t + 1)))} =\\\operatorname{log2}(\operatorname{card}(Omega(0))) - \operatorname{log2}(\operatorname{card}(Omega(n))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/CommitmentDepthTelescoping.finite_plan_commitment_depth_telescopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source object is a finite sequence of compatible future-plan spaces. At each step, commitment depth is constructed as the decrease in its base-two log-cardinality.

The finite sum cancels every intermediate plan-space capacity, leaving only the initial capacity minus the terminal capacity. The result also holds for an empty plan space under Lean's total real logarithm.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/CommitmentDepthTelescoping.finite_plan_commitment_depth_telescopes`
