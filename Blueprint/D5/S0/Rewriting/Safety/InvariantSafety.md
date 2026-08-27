# Invariant Safety

## Abstract

An inductive invariant makes every finitely reachable state safe.

**Theorem 1.1 (Inductive invariants certify finite executions).**

$$\forall X: \operatorname{Type}, R: X \to \left(X \to \operatorname{Prop}\right),\\I0, J, S: \operatorname{Set}(X),\\I0 \subseteq J \land J \subseteq S \land\\(\forall x, y: X, x \in J \land R(x, y) \Rightarrow y \in J)\\\Rightarrow \forall x0, x: X,\\x0 \in I0 \land \operatorname{ReflTransGen}(R)(x0, x) \Rightarrow x \in S.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a transition relation, I0 the initial set, J an invariant, and S the safe set. The hypotheses expose all three invariant conditions: I0 is contained in J, J is contained in S, and every R-successor of a state in J remains in J.

A reflexive-transitive R path represents an arbitrary finite execution. Direct induction with Relation.ReflTransGen.head_induction_on propagates membership in J from the actual initial state to the endpoint, where containment in S gives safety.

Repository and pinned-Mathlib searches found no declaration packaging the complete theorem. The pinned induction primitive is applied directly.

## References

- Truth anchor: `D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety`
