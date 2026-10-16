# Nonempty Finite Cofiltered Limits

## Abstract

A cofiltered limit of nonempty finite sets is nonempty.

## Countable towers and the finite-layer boundary

Given finite nonempty sets X(n) and arbitrary total maps p(n) from X(n+1) to X(n), Functor.ofOpSequence composes the successor maps into a diagram on the opposite of the natural-number order. Apply nonempty_sections_of_finite_inverse_system to this diagram. A section gives x(n) in X(n) with p(n)(x(n+1)) = x(n) for every n. Surjectivity of the successor maps is not a hypothesis. This is the finite inverse-limit theorem of the Stacks Project, tag 086J.

Finiteness cannot be omitted: take X(n) to be the natural numbers at least n and take the transition maps to be inclusions. Every level is nonempty, but compatibility makes all selected natural numbers equal to x(0). The level x(0)+1 then requires x(0)+1 at most x(0), a contradiction.

**Theorem 1.1 (A finite nonempty cofiltered limit is nonempty).**

$$\forall J, F: J \to \operatorname{Set},\ \operatorname{Cofiltered}\left(J\right) \land\ (\forall j\in J, \operatorname{Finite}\left(F(j)\right) \land \operatorname{Nonempty}\left(F(j)\right))\ \Rightarrow \operatorname{Nonempty}\left(\operatorname{inverseLimit}\left(F\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.finite_cofiltered_limit_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a cofiltered category and let F assign a type to every object of J. Assume every assigned type is finite and nonempty.

The inverse limit is represented by the type of sections compatible with every transition map. That section type is nonempty.

The compatible section is an element of the inverse limit. The cofiltered hypothesis permits simultaneous comparison of finitely many indices; finiteness of each component supplies compactness.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.finite_cofiltered_limit_nonempty`
