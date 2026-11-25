# Fifteen settings for a rotor mixture

## Abstract

Ten base-pair comparisons and twenty incident comparisons yield a positive error for any finite fixed-weight mixture of four-dimensional unit rotor readings.

**Definition 1.1 (Ten unordered pairs).**

Lean statement: `D5/S3/Quantum/Rotors/FifteenSettingGap.pairSum`

*Formalization.* `D5/S3/Quantum/Rotors/FifteenSettingGap.pairSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each unordered pair of the five indices is counted once, by choosing its increasing order.

**Theorem 1.2 (Frame energy and the midpoint discrepancy).**

$$D \ge \frac{5}{4(1+\sqrt{2})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Rotors/FifteenSettingGap.fifteen_setting_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Five unit vectors in real dimension four have upper off-diagonal Gram energy at least 5/8. Assign any unit vector to each of the ten pairs. The discrepancy D sums the squared distances between each base-vector sum and the assigned pair vector scaled by the square root of two.

The four-by-four frame operator has trace five. Its squared trace is bounded by four times the trace of its square. Removing the five diagonal squares of the Gram matrix and counting each pair once gives 5/8. The reverse triangle inequality bounds the discrepancy from below even when two base vectors coincide or are antipodal.

**Definition 1.3 (Half-angle comparison probability).**

Lean statement: `D5/S3/Quantum/Rotors/FifteenSettingGap.comparison`

*Formalization.* `D5/S3/Quantum/Rotors/FifteenSettingGap.comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite list of fields, this adds one to their weighted mean dot product and divides by two. For nonnegative weights summing to one it equals the weighted mean of the individual probabilities.

**Theorem 1.4 (A common error bound for thirty comparisons).**

$$\delta \ge \frac{5}{80(1+\sqrt{2})^{2}(2+4\sqrt{2})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Rotors/FifteenSettingGap.fixed_mixture_probability_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite field assigns a real four-dimensional unit vector to each setting. A single array of nonnegative weights summing to one is used for all settings. The target uses five orthonormal directions in real dimension five and the normalized sum of the two directions for each pair. The ten base pairs have probability one half. Each of the twenty incident base-to-pair comparisons has probability (1+1/√2)/2. Every common absolute error bound on those thirty comparisons satisfies the displayed inequality.

Squaring each midpoint discrepancy expresses it as an affine function of the three dot products. Taking a common weighted mean preserves the lower bound on D. If all thirty probability errors are bounded by delta, the mean discrepancy is at most ten times (4+8√2) times delta.

## References

- Truth anchor: `D5/S3/Quantum/Rotors/FifteenSettingGap.comparison`
- Truth anchor: `D5/S3/Quantum/Rotors/FifteenSettingGap.fifteen_setting_gap`
- Truth anchor: `D5/S3/Quantum/Rotors/FifteenSettingGap.fixed_mixture_probability_gap`
- Truth anchor: `D5/S3/Quantum/Rotors/FifteenSettingGap.pairSum`
