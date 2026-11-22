# Short Integer Relations and Weighted Compatible Deletion

## Abstract

Short incompatible integer relations compare the weighted cost of deletion with the common-time sine deficit.

Let S be a nonempty finite set of indices with real frequencies γ and positive weights w on S. A subset U of S is compatible if every integer relation on U has coefficient sum divisible by four. The deleted fraction P is the minimum of the total weight on S minus U divided by the total weight on S over compatible U. The empty subset is compatible. The deficit D is one minus the supremum over t in T of the weighted sine score Σⱼ wⱼ sin(γⱼ t) divided by the total weight. The real time set T contains an upper ray [a,∞) for some real a.

**Theorem 1.1 (Weighted comparison).**

$$\frac{P}{2 \cdot H^{2}} \le D \land \left(D \le 2 \cdot P \land \frac{P}{H^{2}} \le D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume H ≥ 1 and that each incompatible U contains an integer relation of coefficient sum nonzero modulo four and coefficient ℓ¹ length at most H. At each time retain exactly the coordinates with sine loss strictly below 1/H². If a short incompatible relation were supported there, its character on the orbit would be one and its value at the common quarter phase would be a nontrivial fourth root of unity, at distance at least √2 from one. The coordinate chord squared equals twice the sine loss. The character chord bound would therefore give a distance strictly below H · √2/H = √2. The retained set is compatible. Its complement costs at least P of the total weight and each deleted coordinate pays at least 1/H² of its weight.

For any compatible U, the orbit closure on the retained coordinates contains the common quarter phase on every upper ray. The retained score approaches its full weight by continuity. The omitted score is bounded below by minus the omitted weight, so the total loss is at most twice the omitted weight in the infimum. Minimizing over U gives the upper bound independently of the short relation condition.

The short relation condition for finite sets of actual ζ ordinates remains open.

**Theorem 1.2 (Quadratic separation for consecutive frequencies).**

$$P = \frac{1}{2} \land \left(\operatorname{Short}\left(S, g, H\right) \land \left(\frac{1}{4 \cdot H^{2}} \le D \land \left(D \le \frac{\pi^{2}}{8 \cdot H^{2}} \land \frac{1}{2 \cdot H^{2}} \le D\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the frequencies (n,n + 1) with positive integer n and any equal positive weights. The relation (n + 1,−n) has coefficient sum one and length H = 2n + 1. The full pair is incompatible, and every proper subset is compatible, so the short relation condition holds at H and the deleted fraction is 1/2. At time π/H the phases are π/2 ± π/(2H). Adding nonnegative integral multiples of 2π puts this time in any upper ray while preserving the score. The pointwise deficit there is 1 − cos(π/(2H)), at most π²/(8H²). The weighted lower bounds give the two corresponding lower constants.

## References

- Truth anchor: `D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation`
- Truth anchor: `D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds`
- Dependency: [D5/S3/Fourier/WeightedIntegerRelations](WeightedIntegerRelations.md)
- Dependency: [D5/S3/Fourier/WeightedPhaseRelationLattice](WeightedPhaseRelationLattice.md)
