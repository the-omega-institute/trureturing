# Phase Obstructions Across Relation Lengths

## Abstract

Short integer relation obstructions give a simultaneous bound on weighted sine loss.

Let S be a finite set with real frequencies g and real weights w. Write A(t) for the weighted mean of sin(g(j)t) at one common real time t. For any set T of real times, D(T) is one minus the supremum of A(t) over T, with D(∅) = 1. Taking T to be all real times gives the unrestricted deficit. Lean uses zero for a quotient with zero denominator.

**Theorem 1.1 (Minimum omitted weight).**

$$\operatorname{IsLeast}\left(C_{h}, P_{h}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.omissionFraction_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At integer length h, the set Cₕ contains the omitted weight fractions for subsets U of S with the following property. Every integer relation supported on U, with coefficient ℓ¹ norm at most h, has coefficient sum divisible by four. The empty subset is always admissible. The set of candidate fractions is finite, so its infimum Pₕ is attained for arbitrary real weights.

For the phase bounds assume w(j) ≥ 0 on S. Write Sₙ for the sum of (h⁻² − (h+1)⁻²) Pₕ over 1 ≤ h ≤ n and L for the series sum.

**Theorem 1.2 (Simultaneous bound at a common time).**

$$\forall t \in \mathbb{R},\; \forall N \in \mathbb{N},\; S_{N} + \frac{P_{N + 1}}{(N + 1)^{2}} \le 1 - \operatorname{A}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.simultaneous_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each h from 1 through N + 1, retain coordinates whose loss 1 − sin(g(j)t) is strictly below 1/h². A short incompatible relation forces a loss at least 1/h² at one of its coordinates, so the retained set is admissible at h. Its omitted weight bounds Pₕ times the total weight. Give the final threshold the full coefficient 1/(N+1)². For each coordinate, the coefficients of the thresholds it meets or exceeds telescope to a value bounded by its loss.

**Theorem 1.3 (Series, single-length bounds and remainder).**

$$\left(\forall N \in \mathbb{N},\; S_{N} + \frac{P_{N + 1}}{(N + 1)^{2}} \le \operatorname{D}\left(T\right)\right) \land \left(\operatorname{HasSum}\left((n \mapsto (\frac{1}{(n + 1)^{2}} - \frac{1}{(n + 2)^{2}}) \cdot P_{n + 1}), L\right) \land \left(\operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} \le L \land \left(L \le \operatorname{D}\left(T\right) \land \left(\forall N \in \mathbb{N},\; \frac{P_{N + 1}}{(N + 1)^{2}} \le L - S_{N} \land L - S_{N} \le \frac{1}{(N + 1)^{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.aggregate_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common-time inequality gives the finite bound by taking the supremum of A(t) over a nonempty T. For the empty time set, Pₕ ≤ 1 bounds the finite sum and its residual by the corresponding telescoping sum, which equals D(∅) = 1. The nonnegative series terms are bounded by the summable coefficients. In the tail after N, every Pₕ is between Pₙ₊₁ and 1, and the coefficient sum is 1/(N+1)². Taking N = h − 1 and using Sₙ ≥ 0 gives single-length dominance.

**Theorem 1.4 (Strict improvement with three frequencies).**

$$\left(P_{1} = \frac{1}{2} \land \left(P_{2} = \frac{1}{2} \land \left(\forall h \in \mathbb{N},\; 3 \le h \Rightarrow P_{h} = \frac{3}{4}\right)\right)\right) \land \left(\operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} = \frac{1}{2} \land \left(S_{5} = \frac{73}{144} \land \left(\operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} < S_{5} \land \left(L = \frac{19}{36} \land \left(\left(\forall N \in \mathbb{N},\; 2 \le N \Rightarrow S_{N} = \frac{19}{36} - \frac{3}{4 \cdot (N + 1)^{2}}\right) \land \operatorname{IsLeast}\left(\{N: \mathbb{N} \mid \operatorname{sup}_{1 \le h} \frac{P_{h}}{h^{2}} < S_{N}\}, 5\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PhaseObstructionLengths.strict_three_frequency_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use frequencies (0, 1, 2) with weights (1/2, 1/4, 1/4). The relation (1, 0, 0) forces deletion of the zero frequency at every positive length. After that deletion, the shortest nonzero relation on the remaining pair has length three. The relation (0, 2, −1) forces deletion of one more frequency at length three and above, and retaining frequency 1 alone is admissible for all lengths. The single-length supremum is attained at length one. Starting after the second term, the omitted fraction is constant, so telescoping gives the partial sums and the series value. The partial sums are nondecreasing and the fourth is 112/225. The fifth is the first to exceed the single-length supremum.

In particular, for a nonempty finite frequency set, positive weights and all real times, dropping the nonnegative residual gives the original finite inequality. The series comparison and the fifth partial sum give the original infinite and strict finite comparisons. An application to actual zeta cutoffs requires independent relation bounds for the ordinates.

## References

- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.aggregate_bounds`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.omissionFraction_isLeast`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.simultaneous_bound`
- Truth anchor: `D5/S3/Fourier/PhaseObstructionLengths.strict_three_frequency_example`
- Dependency: [D5/S3/Fourier/ShortPhaseRelations](ShortPhaseRelations.md)
