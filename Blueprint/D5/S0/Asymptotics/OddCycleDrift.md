# Odd-Cycle Drift

## Abstract

An odd-length sign reversal forces a real drift value to vanish.

**Theorem 1.1 (Odd-cycle drift vanishes).**

$$\forall ell\in\mathbb{N}, \forall s\in\mathbb{R}, \operatorname{Odd}(ell) \land s={-1}^{ell}s \Rightarrow s=0.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/OddCycleDrift.odd_cycle_drift_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The wrap-around hypothesis says that one traversal of a cycle of length ell multiplies the real drift value by (-1)^ell. Mathlib's parity lemma rewrites this factor to -1 when ell is odd, leaving s = -s; linear arithmetic then forces s = 0.

This is an honest partial closure of the odd-cycle parity clause in source theorem 5.9. Deriving the wrap equation from the periodic recurrence, the closed forms for cycle values, every even-cycle assertion, and all explicit quadratic and numerical certificates remain unresolved subitems.

## References

- Truth anchor: `D5/S0/Asymptotics/OddCycleDrift.odd_cycle_drift_eq_zero`
