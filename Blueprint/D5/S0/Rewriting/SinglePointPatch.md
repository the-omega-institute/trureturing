# Single-Point Patch

## Abstract

A single-point update outside a finite record preserves all recorded values while changing the rule.

**Theorem 1.1 (An update outside the record preserves consistency).**

$$\forall D,Y, [\operatorname{DecidableEq}(D)],\ \forall record \in \operatorname{Finset}(D), \forall prescribed,rule: D \to Y,\ \forall a \in D, \forall b \in Y,\ ((\forall d \in record, rule(d) = prescribed(d)) \land \neg(a \in record) \land b \neq rule(a)) \Rightarrow\ ((\forall d \in record, update(rule,a,b)(d) = prescribed(d)) \land update(rule,a,b) \neq rule).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/SinglePointPatch.update_outside_record_preserves_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let record be a finite set of observed positions, prescribed the observed values, and rule a function agreeing with those observations. If a lies outside record and b differs from rule(a), replacing rule(a) by b leaves every recorded value unchanged and produces a function unequal to rule.

Pinned Mathlib supplies Function.update_of_ne for recorded positions and Function.update_ne_self_iff for the genuine change at a. The theorem is therefore a thin wrapper around the upstream function-update API.

This is an honest partial closure of the leading consistency clause in the source corollary. The program-complexity upper bound and the subsequent population-level semantic commentary remain unresolved.

## References

- Truth anchor: `D5/S0/Rewriting/SinglePointPatch.update_outside_record_preserves_consistency`
