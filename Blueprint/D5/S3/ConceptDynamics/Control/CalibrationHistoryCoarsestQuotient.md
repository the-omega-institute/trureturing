# Destructive Calibration Histories

## Abstract

Destructive experiments solve any pair of calibration histories in one step, but their full union is unsolvable and has no coarsest feasible history encoding.

**Definition 1.1 (Live history classes and retained target cells).**

Lean statement: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.Cell`

*Formalization.* `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Histories are Fin 3, with 0, 1, 2 naming calibration classes 1, 2, 3. A live cell stores a nonempty set of histories and includes both possible target bits at every history. A known cell retains one acquired bit. A dead cell retains both bits after a failed destructive experiment. Known and dead cells describe observer knowledge; the physical device is in the same terminal state in both cases.

**Definition 1.2 (Each experiment has exactly one failing history).**

Lean statement: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.response`

*Formalization.* `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An experiment is named by its failing history. Experiment 0 is c, experiment 1 is a, and experiment 2 is b. It returns no bit when the history equals that index, and otherwise returns the target bit. Thus class 1 succeeds on a and b, class 2 on b and c, and class 3 on a and c.

**Definition 1.3 (Attained replies determine the successor knowledge cell).**

Lean statement: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.calibrationSystem`

*Formalization.* `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.calibrationSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The control system uses the existing ControlSystem and BoundedReachStrategy types. A live experiment branches to exactly the cells represented by responses attained at its possible histories and bits. A bit response produces a known cell; a failed response produces the dead cell. Every later experiment returns failure and preserves the retained target candidates, represented by a self-loop at known or dead cells. The goal consists exactly of known cells. No reset, source copy, calibration archive, or other readout is available.

**Definition 1.4 (Every encoded history class must be solvable).**

Lean statement: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.TaskFeasible`

*Formalization.* `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.TaskFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any history type, control system, goal, and fixed merger of nonempty history sets into control states, an equivalence relation is feasible at horizon n if every one of its classes admits a strategy at that horizon. In the calibration model the merger constructs the live cell. The quotient cardinality counts initial history labels, rather than all states of a running controller. The order S <= R means every S-equivalent pair is R-equivalent, so R is coarser.

**Lemma 1.5 (A bad successor is enough to defeat any bounded strategy).**

$$\begin{gathered}\forall X: \operatorname{Type}, M: \operatorname{ControlSystem}(X), G, B: \operatorname{Set}(X),\\{}(\forall x \in B, \neg(x \in G)) \land (\forall x \in B, \forall u: \operatorname{Action}(M, x), \exists y \in \operatorname{successor}(M, u), y \in B)\\{}\implies \forall n: \operatorname{Nat}, \forall x \in B, \neg\operatorname{BoundedReachStrategy}(M, G, n, x)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.trap_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bad set is disjoint from the goal. At every bad state, every action has at least one bad successor. Induction on a bounded strategy then excludes success: stopping contradicts disjointness, and taking an action lets the environment select the bad successor. This applies to all horizons, rather than just to a table of short protocols.

**Definition 1.6 (The universal coarsest task-sufficient encoding assertion).**

Lean statement: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim`

*Formalization.* `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion quantifies over all small history and state types, control systems with small action types, goals, fixed mergers, and positive finite horizons. Whenever some encoding is feasible, it requires a feasible encoding coarser than every feasible encoding. A greatest encoding would also be unique, because the equivalence-relation order is antisymmetric.

**Theorem 1.7 (Task sufficiency need not have a coarsest feasible quotient).**

$$\neg\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At horizon one, the partitions {1,2}|{3} and {1,3}|{2} are both feasible. A common coarsening puts all three histories in one class. That class has a failed first-experiment branch into the dead cell and is unsolvable. This single history task therefore contradicts the universal assertion.

**Theorem 1.8 (One-step pairwise solvability and failure of a coarsest encoding).**

$$\begin{gathered}(\forall i: \operatorname{Fin}(3), \operatorname{W}(1, \{i\}) \land \neg\operatorname{W}(0, \{i\})) \land\\{}(\forall i, j: \operatorname{Fin}(3), \operatorname{W}(1, \{i, j\}) \land \neg\operatorname{W}(0, \{i, j\})) \land\\{}(\forall n: \operatorname{Nat}, \neg\operatorname{W}(n, \{0, 1, 2\})) \land\\{}(\forall i: \operatorname{Fin}(3), \operatorname{T}(\operatorname{live}(\{i\})) = \operatorname{univ}) \land\\{}(\forall n: \operatorname{Nat}, 1 \leq n \implies ((\exists R, \operatorname{F}(n, R) \land \operatorname{card}(\operatorname{Quotient}(R)) = 2) \land (\forall R, \operatorname{F}(n, R) \implies 2 \leq \operatorname{card}(\operatorname{Quotient}(R))) \land \neg(\exists R, \operatorname{F}(n, R) \land (\forall S, \operatorname{F}(n, S) \implies S \leq R)))) \land\\{}\neg\operatorname{claim}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write W(n,A) for a bounded strategy in the calibration control system with horizon n from the live cell of the nonempty history set A. Write F(n,R) for TaskFeasible in that same system, with the live-cell merger, and T for possibleTargets. All displayed i and j range over Fin 3; R and S range over its equivalence relations.

Every singleton and every pair has an experiment that fails on none of its histories. All attained responses then give a known bit in one step. Stopping at step zero fails because both bits are still possible. For the full union, each first experiment fails on its own history. Both target bits then have the same dead successor, whose self-loop satisfies the bad-set condition for every future depth.

For each positive horizon, the partition {1,2}|{3} gives two feasible classes. A quotient with at most one class identifies all histories and would solve the impossible full union. Thus the minimum is exactly two. A greatest feasible relation would coarsen both {1,2}|{3} and {1,3}|{2}, forcing the same impossible full class. Equal target candidate sets and equal shortest budgets therefore do not justify merging calibration histories.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.Cell`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.TaskFeasible`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.calibrationSystem`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.refutation`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.response`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.result`
- Truth anchor: `D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.trap_general`
- Dependency: [D5/S3/ConceptDynamics/Control/FiniteHorizonReachability](FiniteHorizonReachability.md)
