# Exact rational event budgets

## Abstract

The active orbit columns determine the eventual period of finite equivariant realizations.

**Theorem 1.1 (The eventual period of uniform event budgets).**

$$\exists w, w = mq \land 0 < h \land (\forall N \in D, mh \mid N) \land (\exists C, \forall t, 0 < t \land C \leq t \Rightarrow mht \in D)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group acts on a finite target T. A finite family of events E(i) has prescribed rational masses q(i). Some event is all of T and has prescribed mass one. Assume the orbit event matrix A has a real nonnegative solution of A x = q, with A(i,O) the number of elements of orbit O in event E(i).

Let m be the least common multiple of the reduced denominators. There is an integer vector w with w = m q. An orbit is active if its coordinate is positive in some nonnegative real solution of A x = w. Let M be the integer additive map formed by the active columns and h be the additive order of the class of w modulo the range of M.

D consists of the positive seed budgets. A budget is realized by a finite seed set of that size with a group action and an equivariant map to T. The fraction of seeds mapping to each event is its prescribed mass. Each subgroup fixes a seed exactly when it fixes that seed's image.

Average a feasible vector with witnesses for all active coordinates. Scaling that average and subtracting one at each active coordinate leaves a feasible system with integral right-hand side. The integer optimizer gives a scaled integral solution for this shifted system. Adding back the shift gives a strictly positive integer witness. The integer fiber theorem supplies the order and the eventual tail. The normalization event counts the entire seed set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets`
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts](UniformOrbitCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformTableCalibration](UniformTableCalibration.md)
