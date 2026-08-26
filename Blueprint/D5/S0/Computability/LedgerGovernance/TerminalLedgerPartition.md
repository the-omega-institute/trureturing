# Terminal Ledger Partition

## Abstract

Terminal grades partition the semantic ledger into migrated, wall, and resident sets.

**Theorem 1.1 (Terminal grades give a three-way ledger partition).**

$$\begin{gathered}\forall Statement, Grade: \operatorname{Type},\\{}[\operatorname{Countable}(Statement)], [\operatorname{Finite}(Grade)], [\operatorname{PartialOrder}(Grade)],\\{}\forall \sigma: \operatorname{LedgerHistory}\left(Statement, Grade\right),\\{}(\forall s: Statement, \operatorname{Finite}\left(\operatorname{revisionTimesFrom}\left(\operatorname{enrolledAt}\left(\sigma, s\right), (t: \mathbb{N} \mapsto \operatorname{grade}\left(\sigma, s, t\right))\right)\right)),\\{}\forall Gplus: \operatorname{Set}\left(Grade\right), \forall Sem, W, T: \operatorname{Set}\left(Statement\right),\\{}W \subseteq Sem, \forall forbidden: \mathbb{N} \to Statement \to \operatorname{Prop},\\{}(\forall t: \mathbb{N}, g: Statement, g \in T \Rightarrow \operatorname{grade}\left(\sigma, g, t\right) \in Gplus),\\{}(\forall t: \mathbb{N}, w: Statement, w \in W \Rightarrow \operatorname{grade}\left(\sigma, w, t\right) \in Gplus \Rightarrow (\forall g: Statement, g \in T \Rightarrow \operatorname{grade}\left(\sigma, g, t\right) \in Gplus) \Rightarrow \operatorname{forbidden}(t,w)),\\{}(\forall t: \mathbb{N}, w: Statement, w \in W \Rightarrow \neg \operatorname{forbidden}(t,w))\\{}\Rightarrow \exists! \sigma_{\infty}: Statement \to Grade,\\{}(\forall s, \exists N \geq \operatorname{enrolledAt}(s), \forall t \geq N, \sigma_{t}(s) = \sigma_{\infty}(s)) \land\\{}M = \operatorname{intersection}(Sem,\operatorname{preimage}(\sigma_{\infty},Gplus)), R = Sem \setminus (M \operatorname{union} W),\\{}Sem = M \operatorname{union} W \operatorname{union} R \land\\{}\operatorname{Disjoint}(M,W) \land \operatorname{Disjoint}(M,R) \land \operatorname{Disjoint}(W,R).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/LedgerGovernance/TerminalLedgerPartition.terminal_ledger_three_way_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a countable statement ledger take values in a finite partially ordered grade space, and assume every post-enrollment grade track has finitely many revisions. The pointwise ledger-limit theorem therefore supplies a unique terminal grading.

Let Sem be the terminal semantic domain and W a wall contained in Sem. Every gatekeeper remains positive, joint positivity of a wall statement and all gatekeepers is forbidden, and consistency rules out forbidden wall configurations.

The migrated set M consists exactly of semantic statements with a positive terminal grade. The resident set R is Sem with M and W removed. The imported terminal-grade decomposition theorem gives the displayed cover equality and all three pairwise disjointness claims directly.

## References

- Truth anchor: `D5/S0/Computability/LedgerGovernance/TerminalLedgerPartition.terminal_ledger_three_way_partition`
- Dependency: [D5/S0/Computability/TerminalGradeDecomposition](../TerminalGradeDecomposition.md)
