# Terminal Grade Decomposition

## Abstract

A stabilized guarded ledger partitions its semantic statements into migrated, wall, and resident parts.

**Theorem 1.1 (Terminal grades give a three-way disjoint decomposition).**

$$\operatorname{RepairClause}(history), W \subseteq Sem,\\\forall t, g\in T, \sigma_{t}(g)\in Gplus,\\\forall t, w\in W, (\sigma_{t}(w)\in Gplus \land \forall g\in T, \sigma_{t}(g)\in Gplus) \Rightarrow \operatorname{forbidden}(t,w),\\\forall t, w\in W, \neg\operatorname{forbidden}(t,w)\\\Rightarrow \exists! \sigma_{\infty}: Statement \to Grade, (\forall s, \exists N \geq \operatorname{enrolledAt}(s), \forall t \geq N, \sigma_{t}(s) = \sigma_{\infty}(s)) \land\\M = \operatorname{intersection}(Sem,\operatorname{preimage}(\sigma_{\infty},Gplus)), R = Sem \setminus (M \operatorname{union} W),\\Sem = M \operatorname{union} W \operatorname{union} R \land\\\operatorname{Disjoint}(M,W) \land \operatorname{Disjoint}(M,R) \land \operatorname{Disjoint}(W,R).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/TerminalGradeDecomposition.terminal_grade_three_way_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a countable statement ledger take values in a finite partially ordered grade space, and assume each statement changes grade only finitely often after enrollment. The pointwise ledger-limit theorem supplies a unique terminal grading and a stabilization cutoff for every statement.

Let Sem be the semantic domain, W a wall contained in Sem, T its gatekeepers, and Gplus the positive grades. Assume every gatekeeper remains positive, joint positivity of a wall statement and all gatekeepers is forbidden, and forbidden wall configurations never occur. The guarded-wall theorem makes every wall statement non-positive at every time. Evaluating at its terminal cutoff therefore keeps W disjoint from the terminal-positive migrated part M.

Define M as the semantic statements whose terminal grade lies in Gplus, and define R as Sem with M and W removed. Elementary set extensionality gives Sem = M union W union R. Guarded-wall non-positivity proves M and W are disjoint, while the defining set difference proves that R is disjoint from each. The Boolean witness in the Lean module checks that all assumptions can hold simultaneously.

## References

- Truth anchor: `D5/S0/Computability/TerminalGradeDecomposition.terminal_grade_three_way_decomposition`
- Dependency: [D5/S0/Computability/GuardedWall](GuardedWall.md)
- Dependency: [D5/S0/History/LedgerLimit](../History/LedgerLimit.md)
