# Context Refinement Separates a Coarse Conflict

## Abstract

A refinement separates opposite support hidden by one coarse context.

**Theorem 1.1 (Refinement separates opposite support into distinct contexts).**

$$\forall X, C, D: \operatorname{Type},\ q_{C}: X \to C, q_{D}: X \to D, P: X \to \operatorname{Prop},\ x, y: X,\ q_{C}(x) = q_{C}(y) \land P(x) \land \neg P(y) \land q_{D}(x) \neq q_{D}(y) \Rightarrow\ ((\operatorname{conceptJoin}(q_{C}, q_{D}, x) \neq \operatorname{conceptJoin}(q_{C}, q_{D}, y)) \land\ (\neg \exists b: C \times D, \operatorname{conceptJoin}(q_{C}, q_{D}, x) = b \land P(x) \land \operatorname{conceptJoin}(q_{C}, q_{D}, y) = b \land \neg P(y)) \land\ (\exists d_{p}, d_{n}: D, d_{p} \neq d_{n} \land q_{D}(x) = d_{p} \land P(x) \land q_{D}(y) = d_{n} \land \neg P(y)) \land\ (\exists c: C, \exists d_{p}, d_{n}: D, d_{p} \neq d_{n} \land q_{C}(x) = c \land q_{D}(x) = d_{p} \land P(x) \land q_{C}(y) = c \land q_{D}(y) = d_{n} \land \neg P(y))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ContextRefinementConflictSeparation.context_refinement_separates_conflict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coarse and refinement contexts are the canonical concept readouts. The joined context is constructed with the existing product readout, so this theorem extends the family source of truth.

All four source clauses are public: joined-fiber separation, exclusion from one joined context, positive and negative support in distinct refinement coordinates, and their shared coarse coordinate.

Repository and pinned-Mathlib searches found no theorem combining fiber separation with opposite predicate support. The proof applies the canonical conceptJoin and product projection directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ContextRefinementConflictSeparation.context_refinement_separates_conflict`
