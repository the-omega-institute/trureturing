# Terminal Grade Decomposition

## Abstract

A stabilized guarded ledger partitions its semantic statements into migrated, wall, and resident parts.

**Theorem 1.1 (Terminal grades give a three-way disjoint decomposition).**

$$\forall Statement \in Type, Grade \in Type,\; \left(\left(\operatorname{Countable}\left(Statement\right) \land \operatorname{Finite}\left(Grade\right)\right) \land \operatorname{PartialOrder}\left(Grade\right)\right) \Rightarrow \left(\forall history \in \operatorname{LedgerHistory}\left(Statement, Grade\right),\; \left(\forall statement \in Statement,\; \operatorname{Finite}\left(\operatorname{revisionTimesFrom}\left(\operatorname{enrolledAt}\left(history, statement\right), \operatorname{grade}\left(history, statement\right)\right)\right)\right) \Rightarrow \left(\forall positiveGrades \in \operatorname{Set}\left(Grade\right),\; \forall semantic \in \operatorname{Set}\left(Statement\right), wall \in \operatorname{Set}\left(Statement\right), gatekeepers \in \operatorname{Set}\left(Statement\right),\; \forall forbidden \in Nat \to \left(Statement \to Prop\right),\; \left(\left(\left(wall \subseteq semantic \land \left(\forall t \in Nat, g \in Statement,\; g \in gatekeepers \Rightarrow \operatorname{grade}\left(history, g, t\right) \in positiveGrades\right)\right) \land \left(\forall t \in Nat, w \in Statement,\; w \in wall \Rightarrow \left(\operatorname{grade}\left(history, w, t\right) \in positiveGrades \Rightarrow \left(\left(\forall g \in Statement,\; g \in gatekeepers \Rightarrow \operatorname{grade}\left(history, g, t\right) \in positiveGrades\right) \Rightarrow \operatorname{forbidden}\left(t, w\right)\right)\right)\right)\right) \land \left(\forall t \in Nat, w \in Statement,\; w \in wall \Rightarrow \left(\neg \operatorname{forbidden}\left(t, w\right)\right)\right)\right) \Rightarrow \exists! terminalGrade: Statement \to Grade, (\forall statement \in Statement,\; \exists cutoff \in Nat,\; \operatorname{enrolledAt}\left(history, statement\right) \le cutoff \land \left(\forall t \in Nat,\; t \ge cutoff \Rightarrow \operatorname{grade}\left(history, statement, t\right) = terminalGrade\left(statement\right)\right)) \land \\{}migrated = \operatorname{intersection}(semantic,\operatorname{preimage}(terminalGrade,positiveGrades)), resident = semantic \setminus (migrated \operatorname{union} wall),\\{}semantic = migrated \operatorname{union} wall \operatorname{union} resident \land\\{}\operatorname{Disjoint}(migrated,wall) \land \operatorname{Disjoint}(migrated,resident) \land \operatorname{Disjoint}(wall,resident)).\right)\right)$$

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
