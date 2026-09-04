# Negative-Exponent Pole Transport

## Abstract

A negative dictionary exponent transports a positive-order zero into an exact pole debt.

**Theorem 1.1 (Negative exponents transport zeros to pole debts).**

$$\operatorname{ord}_{s_0}(\prod_{i\in S}f_i^{e_i})=e_d m+\sum_{i\in S\setminus{d}}e_i \operatorname{ord}_{s_0}(f_i),\quad \neg \operatorname{Pole}(s_0)\iff 0\leq \operatorname{ord}_{s_0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NegativeExponentPoleTransport.negative_exponent_pole_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of complex meromorphic factors carry integer exponents. If a distinguished factor has positive local order m and its exponent e_d is negative, then its contribution e_d m is strictly negative. The order of the whole product is exactly this pole debt plus the sum of the remaining factor orders.

Mathlib's punctured-neighborhood criterion then gives both sides: the dictionary product tends to infinity exactly when that total order is negative, and it has no pole exactly when the total order is nonnegative. Thus every possible cancellation is exposed in the remaining finite sum rather than hidden in an analytic slogan.

This is the exact structural content that can be certified from the source atom. Its claims about scaled Riemann-zeta zeros, an RH-based exclusion, Hecke-Mahler factor windows, numerical residues, and the three named bricks require external analytic and computational certificates not present in the atom. They are therefore omitted, not promoted to assumptions or asserted without proof. The proof directly uses meromorphicOrderAt_prod, meromorphicOrderAt_zpow, and tendsto_cobounded_iff_meromorphicOrderAt_neg from pinned Mathlib.

## References

- Truth anchor: `D5/S3/Analytic/NegativeExponentPoleTransport.negative_exponent_pole_transport`
