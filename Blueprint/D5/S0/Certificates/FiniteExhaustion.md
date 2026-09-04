# Finite Exhaustion Certificates

## Abstract

Finite Boolean search results are reflected into exact universal validity and unsatisfiability statements.

**Theorem 1.1 (A successful exhaustive refutation excludes every witness).**

$$\operatorname{exhaustiveUnsatCheck}(P) = true \Rightarrow \neg \exists x, P(x) = true.$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteExhaustion.unsatisfiable_of_exhaustive_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checker uses the finite decidability instance to evaluate whether a Boolean predicate is false on every point of its finite domain.

The reflection theorem identifies the returned Boolean with the corresponding universal proposition.

A true refutation result can therefore be eliminated inside Lean as a proof that no satisfying assignment exists.

## References

- Truth anchor: `D5/S0/Certificates/FiniteExhaustion.unsatisfiable_of_exhaustive_check`
