# Guarded Wall Persistence

## Abstract

A guarded wall stays outside positive grades at every time and in the unique ledger limit.

**Theorem 1.1 (A guarded wall persists in the ledger limit).**

$$\begin{gathered}\operatorname{Countable}(Statement), \operatorname{Finite}(Grade), \operatorname{PartialOrder}(Grade),\\{}\operatorname{FiniteRevisions}(history),\\{}(\forall t, g \in T, \sigma_{t}(g) \in Gplus),\\{}(\forall t, w \in W, \sigma_{t}(w) \in Gplus \land \forall g \in T, \sigma_{t}(g) \in Gplus \Rightarrow \operatorname{forbidden}(t,w)),\\{}(\forall t, w \in W, \neg \operatorname{forbidden}(t,w))\\{}\Rightarrow (\forall t, w \in W, \neg (\sigma_{t}(w) \in Gplus)) \land\\{}\exists! \sigma_{\infty}: Statement \to Grade,\\{}(\forall s, \exists N \geq \operatorname{enrolledAt}(s), \forall t \geq N, \sigma_{t}(s) = \sigma_{\infty}(s)) \land\\{}(\forall w \in W, \neg (\sigma_{\infty}(w) \in Gplus)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/LedgerGovernance/GuardedWallPersistence.guarded_wall_persists_in_ledger_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a countable ledger take values in a finite partially ordered grade space, and assume every post-enrollment grade track has only finitely many revisions. Let W be the guarded wall, T its gatekeepers, and Gplus the positive grades.

Every gatekeeper remains positive. Joint positivity of a wall statement and all gatekeepers is declared forbidden, while consistency rules out every such forbidden configuration. The existing guarded-wall theorem therefore excludes W from Gplus at every finite time.

The existing ledger-limit theorem supplies the unique terminal grading. Evaluating finite-time wall exclusion at each statement's stability cutoff proves that every wall statement remains outside Gplus in that terminal grading.

## References

- Truth anchor: `D5/S0/Computability/LedgerGovernance/GuardedWallPersistence.guarded_wall_persists_in_ledger_limit`
- Dependency: [D5/S0/Computability/GuardedWall](../GuardedWall.md)
- Dependency: [D5/S0/History/LedgerLimit](../../History/LedgerLimit.md)
