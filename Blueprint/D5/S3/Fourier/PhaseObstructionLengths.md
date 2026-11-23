# Phase Obstructions Across Relation Lengths

## Abstract

Short integer relation obstructions give a simultaneous bound on weighted sine loss.

Let S be a finite set with real frequencies g and nonnegative weights w. Write A(t) for the weighted mean of sin(g(j)t) at one common real time t. For a nonempty time set T, D(T) is one minus the supremum of A(t) over T. Taking T to be all real times gives the unrestricted deficit. Lean uses zero for a quotient with zero denominator.

**Theorem 1.1 (Minimum omitted weight).**

$$\operatorname{IsLeast}\left(C_{h}, P_{h}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.omissionFraction_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At integer length h, the set Cₕ contains the omitted weight fractions for subsets U of S with the following property. Every integer relation supported on U, with coefficient ℓ¹ norm at most h, has coefficient sum divisible by four. The empty subset is always admissible. The set of candidate fractions is finite, so its infimum Pₕ is attained.

**Theorem 1.2 (Simultaneous bound at a common time).**

$$\forall t \in \mathbb{R},\; \forall N \in \mathbb{N},\; \sum_{1 \le h \leq N} (\frac{1}{h^{2}} - \frac{1}{(h + 1)^{2}}) \cdot P_{h} \le 1 - \operatorname{A}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.simultaneous_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each h from 1 through N, retain coordinates whose loss 1 − sin(g(j)t) is strictly below 1/h². The large-loss inequality for a short relation makes this retained set admissible at h. The weight omitted therefore bounds Pₕ times the total weight. For each coordinate the threshold levels it meets or exceeds form a final segment of the finite sum. Its charge telescopes and is bounded by that coordinate's loss. Summing these charges proves the inequality at the original time t, including N = 0.

**Theorem 1.3 (Series and single-length bounds).**

$$\left(\forall N \in \mathbb{N},\; \sum_{1 \le h \leq N} (\frac{1}{h^{2}} - \frac{1}{(h + 1)^{2}}) \cdot P_{h} \le \operatorname{D}\left(T\right)\right) \land \left(\operatorname{Tendsto}\left((N \mapsto \sum_{1 \le h \leq N} (\frac{1}{h^{2}} - \frac{1}{(h + 1)^{2}}) \cdot P_{h}), \infty, L\right) \land \left(\operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} \le L \land L \le \operatorname{D}\left(T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.aggregate_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terms are nonnegative and the finite sums are bounded by D(T), so the series converges to L. Since Pₕ is nondecreasing, the series tail from h is at least Pₕ times the telescoping sum of the coefficients from h, which equals 1/h².

**Theorem 1.4 (Strict improvement with three frequencies).**

$$\left(P_{1} = \frac{1}{2} \land \left(P_{2} = \frac{1}{2} \land \left(\forall h \in \mathbb{N},\; 3 \le h \Rightarrow P_{h} = \frac{3}{4}\right)\right)\right) \land \left(\operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} = \frac{1}{2} \land \left(\sum_{1 \le h \leq 5} (\frac{1}{h^{2}} - \frac{1}{(h + 1)^{2}}) \cdot P_{h} = \frac{73}{144} \land \operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} < \sum_{1 \le h \leq 5} (\frac{1}{h^{2}} - \frac{1}{(h + 1)^{2}}) \cdot P_{h}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.strict_three_frequency_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use frequencies (0, 1, 2) with weights (1/2, 1/4, 1/4). The relation (1, 0, 0) forces deletion of the zero frequency at every positive length. After that deletion, the shortest nonzero relation on the remaining pair has length three. The relation (0, 2, −1) forces deletion of one more frequency at length three and above, and retaining frequency 1 alone is admissible for all lengths. The single-length supremum is attained at length one. The fifth partial sum exceeds it by 1/144.

## References

- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.aggregate_bounds`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.omissionFraction_isLeast`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.simultaneous_bound`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.strict_three_frequency_example`
- Dependency: [D5/S3/Fourier/ShortPhaseRelations](ShortPhaseRelations.md)
