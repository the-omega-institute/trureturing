# Exact rational event budgets

## Abstract

The active orbit columns classify exact finite equivariant budgets and give a sufficient cutoff.

**Theorem 1.1 (Exact uniform event budgets and their eventual period).**

$$\begin{aligned}\exists w, w = mq \land 0 < h \land\\(\forall N > 0, N \in D \iff \exists k, n, N = mk \land n \geq 0 \land Mn = kw) \land\\(\forall N \in D, mh \mid N) \land\\(\exists B, p, b, 0 < B \land 0 < p \land Mp = Bw \land B = hb \land\\(\exists u, Mu = hw) \land (\forall u, Mu = hw \Rightarrow \forall t > 0, \\(b-1)b(1 + \sum_{j} \Vert u_{j}\Vert) \leq t \Rightarrow mht \in D))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group acts on a finite target T. A finite family of events E(i) has prescribed rational masses q(i). Some event is all of T and has prescribed mass one. Assume the orbit event matrix A has a real nonnegative solution of A x = q, with A(i,O) the number of elements of orbit O in event E(i).

Let m be the least common multiple of the reduced denominators. There is an integer vector w with w = m q. An orbit is active if its coordinate is positive in some nonnegative real solution of A x = w. Let M be the integer additive map formed by the active columns and h be the additive order of the class of w modulo the range of M.

D consists of the positive seed budgets. A budget is realized by a finite seed set of that size with a group action and an equivariant map to T. The fraction of seeds mapping to each event is its prescribed mass. Each subgroup fixes a seed exactly when it fixes that seed's image.

For each positive budget N, the equation uses a natural degree k and a nonnegative integer vector n on the active orbit set J. Every realized budget is divisible by m h.

A positive degree B admits an integer vector p that is strictly positive on J. Write B = h b. There exists a signed integer vector u with M u = h w. For each such u the displayed cutoff applies to every positive normalized degree t.

Average a feasible vector with witnesses for all active coordinates. Scaling that average and subtracting one at each active coordinate leaves a feasible system with integral right-hand side. The integer optimizer gives a scaled integral solution for this shifted system. Adding back the shift gives a strictly positive integer witness. The integer fiber theorem supplies the order and the eventual tail. The normalization event counts the entire seed set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets`
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts](UniformOrbitCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/UniformTableCalibration](UniformTableCalibration.md)
