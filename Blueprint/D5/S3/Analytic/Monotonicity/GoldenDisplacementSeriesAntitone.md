# Golden Displacement Series Antitonicity

## Abstract

The golden displacement sum decreases when either parameter increases.

**Theorem 1.1 (Coordinatewise parameter increases lower the displacement sum).**

$$\forall s_1, w_1, s_2, w_2 \in \mathbb{R},\quad\operatorname{Summable}(\operatorname{dTerm}(s_1, w_1)) \land s_1 \leq s_2 \land w_1 \leq w_2 \Rightarrow\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s_2, w_2, n) \leq \sum_{n=0}^{\infty} \operatorname{dTerm}(s_1, w_1, n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesAntitone.golden_displacement_series_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a parameter pair (s1,w1) where dTerm is summable. If s1 is at most s2 and w1 is at most w2, then the sum at (s2,w2) is at most the sum at (s1,w1). Only summability of the smaller pair is assumed.

At every positive index, both n and nS(n) are at least one. The ordered-exponent theorem for real powers therefore shows that negating and increasing either parameter lowers its factor. The index-zero terms agree, and multiplication preserves the two factor inequalities because all real-power factors are nonnegative.

The exact two-constraint characterization of the convergence region shows that the larger pair is summable: both affine constraints increase under the coordinatewise parameter inequalities. Termwise comparison then passes to the sums via Summable.tsum_le_tsum.

The implication form avoids a redundant larger-pair summability hypothesis that an AntitoneOn interface would require. Setting either parameter inequality to equality gives antitonicity in the other parameter on every convergent upper ray.

The theorem does not claim strict decrease, an equality characterization, a quantitative rate, a converse, or any finite value or order statement outside the exact convergence region.

## References

- Truth anchor: `D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesAntitone.golden_displacement_series_antitone`
