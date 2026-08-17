# Nonempty Finite Cofiltered Limits

## Abstract

A cofiltered limit of nonempty finite sets is nonempty.

**Theorem 1.1 (A finite nonempty cofiltered limit is nonempty).**

$$\forall J, F: J \to \operatorname{Set},\ \operatorname{Cofiltered}\left(J\right) \land\ (\forall j\in J, \operatorname{Finite}\left(F(j)\right) \land \operatorname{Nonempty}\left(F(j)\right))\ \Rightarrow \operatorname{Nonempty}\left(\operatorname{inverseLimit}\left(F\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.finite_cofiltered_limit_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a cofiltered category and let F assign a type to every object of J. Assume every assigned type is finite and nonempty.

The inverse limit is represented by the type of sections compatible with every transition map. That section type is nonempty.

Pinned Mathlib already proves this exact statement as nonempty_sections_of_finite_cofiltered_system. The Lean declaration imports and applies that theorem directly; repository search found only a related specialization to invariant candidate subsets.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.finite_cofiltered_limit_nonempty`
