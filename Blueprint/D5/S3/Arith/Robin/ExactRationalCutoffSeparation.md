# Exact rational cutoff separation

## Abstract

The exact rational cutoff forms at a fixed clock have a positive quantitative logarithmic gap.

**Theorem 1.1 (A logarithmic gap for the exact integer labels).**

Lean statement: `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.cutoff_resonance_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.cutoff_resonance_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m, h, p and j be natural numbers with 0 < h < m, h < p < 3h and 0 < j. Set U = 2^p m^(p − h)(m + p)^h and W = j^h(m + h)^p. Then U ≠ W and 1/max(U, W) ≤ |p log(2m/(m + h)) − h log(jm/(m + p))|. The powers defining U and W are natural-number powers. The lower bound and logarithmic expression use real division and natural logarithms.

Write A = 2m/(m + h) and C = jm/(m + p) as positive rationals. If A^p = C^h, divide the exponents by gcd(h, p) to get coprime H and P with H < P < 3H. There is then a reduced positive rational u/v with (u/v)^H = A and (u/v)^P = C. Eliminating m and clearing denominators gives (P − H)u^P + jHv^P = 2P u^(P − H)v^H. Coprimality forces v^H to divide P − H. If v ≥ 2 then v^H ≥ 2^H ≥ 2H > P − H. Thus v = 1, which is incompatible with 1 < (u/v)^H = A < 2.

The ratio U/W equals A^p/C^h, so U and W are distinct positive integers. For V = max(U, W) and v = min(U, W), the absolute logarithmic difference equals log(V/v). The inequality log(V/v) ≥ 1 − v/V and the integer gap V − v ≥ 1 give the stated lower bound.

**Theorem 1.2 (Short denominators force a larger mode-three residual).**

Lean statement: `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.mode_three_short_denominator_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.mode_three_short_denominator_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take natural numbers m, h, p with 0 < h < min(m, p) and 5p ≤ 8h. If L ≥ exp(50), m ≤ 2hL, h ≤ L/(50 log L), C ≥ 1 and 1500 log(2C) < L, the mode-three absolute logarithmic gap strictly exceeds C times the sum of exp(−L/15)/L² and h exp(−L/3).

Shortness gives m + p ≤ L². Bounding both integer powers separately gives log(max(U, W)) ≤ 33L/500. The lower bound from the exact separation and the two residual terms then contradict each other. The estimate includes the term h exp(−L/3) from the literal cutoff.

## References

- Truth anchor: `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.cutoff_resonance_separation`
- Truth anchor: `D5/S3/Arith/Robin/ExactRationalCutoffSeparation.mode_three_short_denominator_exclusion`
