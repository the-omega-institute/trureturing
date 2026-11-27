# Exact Fourth-Root Gaps

## Abstract

Exact fourth-root character gaps give a finite step lower bound on the common-time sine deficit.

Let S be a finite subset of an index type J with real frequencies g and weights w. An incompatible relation is an integer vector k whose frequency sum is zero and whose coefficient sum is indivisible by four. Its support consists of the coordinates in S with nonzero coefficients, and its length is the sum of their absolute values. The threshold τ is the squared chord gap from 1 to i raised to the coefficient sum, divided by twice the squared length. Write R(k) for incompatibility, V(k) for support, len(k) for length and M(v) for the support maximum. The sine loss E(t,j) is 1 − sin(g(j)t). Write C(x) for the candidate omitted weight fractions and Q(x) for their minimum. A(t) is the weighted sine average and D(T) is one minus its supremum over T. The integral bounds and length comparisons assume nonnegative weights. The support, minimum and partition assertions allow arbitrary real weights.

**Theorem 1.1 (Exact coordinate loss at a common time).**

$$\forall k \in \mathbb{Z}^{J},\; \operatorname{R}\left(k\right) \Rightarrow \left(\forall t \in \mathbb{R},\; 0 < \operatorname{len}\left(k\right) \land \left(\left(0 < \tau (k) \land \tau (k) \le 2\right) \land \left(\exists j \in J,\; j \in \operatorname{V}\left(k\right) \land \tau (k) \le \operatorname{E}\left(t, j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.coordinate_loss_same_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relation has positive length and its threshold lies in (0, 2]. Choose a support coordinate of maximal loss. Apply the weighted character chord estimate to the orbit and the quarter-phase target. Bound the sum of the chord lengths by the coefficient length times the maximal chord. Squaring and using the chord-sine identity yields the loss threshold at that coordinate.

**Theorem 1.2 (Attainment on each exact support).**

$$\forall v \in \operatorname{Finset}\left(J\right),\; \left(\operatorname{M}\left(v\right) = 0 \land \neg {\exists k \in \mathbb{Z}^{J},\; \operatorname{R}\left(k\right) \land \operatorname{V}\left(k\right) = v}\right) \lor \left(\exists k \in \mathbb{Z}^{J},\; \left(\operatorname{R}\left(k\right) \land \operatorname{V}\left(k\right) = v\right) \land \left(\operatorname{M}\left(v\right) = \tau (k) \land \left(0 < \operatorname{M}\left(v\right) \land \left(\forall r \in \mathbb{Z}^{J},\; \operatorname{R}\left(r\right) \Rightarrow \left(\operatorname{V}\left(r\right) = v \Rightarrow \tau (r) \le \operatorname{M}\left(v\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.supportMaximum_zero_or_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonempty residue class of the coefficient sum modulo four, choose a relation of minimum positive integer length. The numerator is constant within the class. The attained maximum over these finitely many candidates is the support maximum. The squared gaps of incompatible residues are 2 and 4. An empty support family contributes the default zero.

**Theorem 1.3 (Minimum omitted weight at each threshold).**

$$\forall x \in \mathbb{R},\; \operatorname{IsLeast}\left(\operatorname{C}\left(x\right), \operatorname{Q}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.least_hitting_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At threshold x, the omitted set meets every incompatible relation support whose threshold is at least x. Each candidate fraction is the weight of the omitted set divided by the total weight of S. Retaining the empty set gives a candidate.

**Theorem 1.4 (Finite partition into intervals of constant cost).**

$$\operatorname{PairwiseDisjoint}\left(B, I\right) \land \left(\operatorname{Union}\left(B, I\right) = (0,2] \land \left(\forall b \in \mathbb{R},\; b \in B \Rightarrow \left(\forall x \in \mathbb{R},\; x \in \operatorname{I}\left(b\right) \Rightarrow \operatorname{Q}\left(x\right) = \operatorname{Q}\left(b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.breakpoint_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Add 0 and 2 to the maxima of all exact supports in the powerset of S. For a positive threshold, a retained subset is admissible precisely when every support it contains has maximum strictly below the threshold. On each interval from one cut to the next, exclude the left endpoint and include the right endpoint. Write B for the nonzero cuts, prev(b) for the cut preceding b and I(b) for the cell ending at b. The active support family is constant throughout each cell.

**Theorem 1.5 (Exact finite sum for the integral).**

$$\int_{0}^{2} \operatorname{Q}\left(x\right) dx = \sum_{b \in B} (b - \operatorname{prev}\left(b\right)) \cdot \operatorname{Q}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.finite_step_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the width of each interval times the omission fraction at its right endpoint.

**Theorem 1.6 (Integrated bound at a common time).**

$$\forall t \in \mathbb{R},\; \int_{0}^{2} \operatorname{Q}\left(x\right) dx \le 1 - \operatorname{A}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.integrated_Q_same_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At one real time t, the coordinates whose sine loss is at least x meet all active supports. Integrating the resulting weight tail gives the normalized sum of coordinate losses, by integrating each coordinate's interval indicator. If total weight is zero, every omission fraction is zero by Lean's division convention.

**Theorem 1.7 (Integrated bound over the allowed times).**

$$\forall T \in \mathcal{P}(\mathbb{R}),\; \int_{0}^{2} \operatorname{Q}\left(x\right) dx \le \operatorname{D}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.integrated_Q_le_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty set T of allowed real times, take the supremum of the normalized sine average. For empty T the deficit is 1 and the same-time bound at zero applies.

**Theorem 1.8 (Comparison with partial length sums).**

$$\forall n \in \mathbb{N},\; \sum_{h = 1}^{n} \operatorname{T}\left(h\right) + \frac{\operatorname{P}\left(n + 1\right)}{(n + 1)^{2}} \le \int_{0}^{2} \operatorname{Q}\left(x\right) dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.partial_length_le_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An incompatible relation of length at most h has threshold at least 1/h². Throughout the inverse-square interval ending at 1/h², the exact threshold cost bounds the minimum omission fraction at length h. Integrate the inequality over the adjacent intervals. The interval from 0 to the next threshold supplies the single-scale residual. Write P(h) for the omitted fraction for incompatible relations of length at most h and T(h) for (h⁻² − (h+1)⁻²)P(h). The full series L sums T(h) over positive integer lengths.

**Theorem 1.9 (Comparison with the length series).**

$$L \le \int_{0}^{2} \operatorname{Q}\left(x\right) dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.length_series_le_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the limit of the bounded partial sums using convergence of the length series.

**Theorem 1.10 (Exact cost for frequencies (1, 3)).**

$$\forall x \in \mathbb{R},\; \left(x \le \frac{1}{8} \Rightarrow \operatorname{Q}\left(x\right) = \frac{1}{2}\right) \land \left(\frac{1}{8} < x \Rightarrow \operatorname{Q}\left(x\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.pair_exact_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any common positive weight, every incompatible relation uses both coordinates and has length at least four. The relation (3, −1) has length four and squared chord gap four, so the threshold is exactly 1/8. At or below it one of the two equal-weight coordinates must be omitted. Above it no omission is needed.

**Theorem 1.11 (Strict improvement for frequencies (1, 3)).**

$$L = \frac{1}{32} \land \left(\int_{0}^{2} \operatorname{Q}\left(x\right) dx = \frac{1}{16} \land L < \int_{0}^{2} \operatorname{Q}\left(x\right) dx\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ExactFourthRootGaps.pair_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With equal positive weights, the interval of cost 1/2 yields an integral of 1/16. The length-only omission fraction is 1/2 from length four onward and zero at smaller lengths. The weighted series telescopes to 1/32.

These bounds apply to any finite real frequency system satisfying the stated weight conditions. A quantitative application to actual zeta ordinates requires separate evidence about which incompatible relations hold, their supports and their coefficient lengths.

## References

- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.breakpoint_partition`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.coordinate_loss_same_time`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.finite_step_integral`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.integrated_Q_le_deficit`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.integrated_Q_same_time`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.least_hitting_weight`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.length_series_le_integral`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.pair_exact_Q`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.pair_strict`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.partial_length_le_integral`
- Truth anchor: `D5/S3/Fourier/ExactFourthRootGaps.supportMaximum_zero_or_attained`
- Dependency: [D5/S3/Fourier/PhaseObstructionLengths](PhaseObstructionLengths.md)
