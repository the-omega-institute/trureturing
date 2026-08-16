# Vanishing Remainder Negativity

## Abstract

A negative limit remains eventually negative after adding a vanishing remainder.

**Theorem 1.1 (A vanishing remainder preserves eventual negativity).**

$$a_n \to -c, r_n \to 0, c > 0 \Rightarrow \exists N, \forall n \ge N, a_n + r_n < 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Limits/VanishingRemainderNegativity.vanishing_remainder_eventually_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a_n converge to -c for a strictly positive real c, and let r_n converge to zero. Continuity of addition makes a_n + r_n converge to -c, and the strict inequality -c < 0 then holds eventually.

This closes only the asymptotic dominance clause of the source atom. It does not construct zeta test functions or formalize the decomposition of the quadratic functional into orbit, prime, and archimedean terms.

## References

- Truth anchor: `D5/S3/Analytic/Limits/VanishingRemainderNegativity.vanishing_remainder_eventually_negative`
