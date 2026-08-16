# Zero-Density Exponent Crossover

## Abstract

The Guth-Maynard density exponent wins exactly between the two classical crossovers.

**Theorem 1.1 (The Guth-Maynard exponent dominates exactly on the crossover interval).**

$$\forall \varepsilon \in \mathbb{R},\ 0 \leq \varepsilon < \frac{1}{2},\ (\frac{30 (\frac{1}{2} - \varepsilon)}{13} \leq \frac{3 (\frac{1}{2} - \varepsilon)}{\frac{3}{2} - \varepsilon} \land \frac{30 (\frac{1}{2} - \varepsilon)}{13} \leq \frac{3 (\frac{1}{2} - \varepsilon)}{\frac{1}{2} + 3\varepsilon}) \Leftrightarrow (\frac{1}{5} \leq \varepsilon \land \varepsilon \leq \frac{4}{15}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Density/ZeroDensityCrossover.guth_maynard_dominates_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source records the Ingham, Huxley, and Guth-Maynard zero-density exponents. After writing the depth as epsilon = sigma - 1/2, their two exact crossover points are epsilon = 1/5 and epsilon = 4/15.

Pinned Mathlib supplies div_le_div_iff0 for positive denominators. The Lean proof checks positivity on 0 <= epsilon < 1/2, applies that library equivalence to both comparisons, and closes the resulting polynomial inequalities.

This theorem closes only the exact algebraic comparison of the three displayed exponent formulas. It does not prove the analytic zero-density estimates themselves, the numerical census table, or any stated RH or Lindelof consequence.

## References

- Truth anchor: `D5/S3/Zeros/Density/ZeroDensityCrossover.guth_maynard_dominates_iff`
