# Guarded Ranking Termination

## Abstract

A well-founded rank forbids infinite guard-preserving transition chains.

**Theorem 1.1 (A decreasing rank terminates guarded transitions).**

$$\forall X, W: Type, guard: X \to Prop, step: X \to X \to Prop,\\{}rank: X \to W, less: W \to W \to Prop,\\{}(\operatorname{IsWellFounded}(W, less) \land (\forall x, y: X, (guard(x) \land step(x, y)) \Rightarrow less(rank(y), rank(x)))) \Rightarrow \forall trajectory: Nat \to X, \exists n: Nat, \neg (guard(trajectory(n)) \land step(trajectory(n), trajectory(n + 1))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/GuardedRankingTermination.guarded_ranking_terminates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source transition is constructed from two independent primitives: `guard x` enables execution at the current state, and `step x y` relates that state to its successor.

Every enabled step strictly lowers `rank` according to the named well-founded relation `less`. The conclusion quantifies over every candidate trajectory and finds an adjacent pair where the guarded transition fails.

The proof directly applies the pinned library theorem `WellFounded.not_rel_apply_succ` to the ranked trajectory. No transition or rank object is defined from the conclusion.

A natural-number countdown checks that the hypotheses admit a nonempty guarded transition relation and instantiates the public theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/GuardedRankingTermination.guarded_ranking_terminates`
