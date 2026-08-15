# Quotient Future Relation

## Abstract

A preserved equivalence is recovered from all future quotient observations.

**Theorem 1.1 (Future quotient observations recover the relation).**

$$\forall Y, tau: Y \to Y,\ R: \operatorname{Setoid}(Y),\ (\forall y, y',\ R(y, y') \Rightarrow R(tau(y), tau(y'))) \Rightarrow \forall y, y',\ ((\forall k\in\mathbb{N},\ [tau^{k}(y)]_{R} = [tau^{k}(y')]_{R}) \iff R(y, y')).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/QuotientFutureRelation.quotient_future_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be an equivalence relation preserved by a self-map tau. Two points have equal quotient classes after every finite number of steps exactly when they were R-related initially. The reverse direction uses preservation repeatedly; the forward direction is already forced by the zeroth observation.

The pinned library search found Quotient.eq' as the exact characterization of equality between quotient classes. Searches for the complete all-future statement and for an arbitrary relation-preservation iterate theorem found no exact declaration. The proof applies the quotient characterization and performs only the remaining one-step induction locally.

The statement is general in the carrier and does not require its finiteness. It asserts only recovery of the chosen preserved equivalence from quotient observations; no classification or existence claim is included.

## References

- Truth anchor: `D5/S0/Rewriting/QuotientFutureRelation.quotient_future_relation_iff`
