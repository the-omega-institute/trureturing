# Short Integer Relations and Weighted Compatible Deletion

## Abstract

Short incompatible integer relations compare the weighted cost of deletion with the common-time sine deficit.

Let S be a finite set of indices with real frequencies γ and nonnegative weights w on S. The total weight is positive so the normalized quantities are defined. A subset U of S is compatible if every integer relation on U has coefficient sum divisible by four. The deleted fraction P is the minimum of the total weight on S minus U divided by the total weight on S over compatible U. The empty subset is compatible. The deficit D is one minus the supremum over t in T of the weighted sine score Σⱼ wⱼ sin(γⱼ t) divided by the total weight.

**Theorem 1.1 (Weighted comparison).**

$$(\forall H \in \mathbb{R},\; \left(T \ne \emptyset \land \left(0 < H \land \operatorname{Short}\left(S, g, H\right)\right)\right) \Rightarrow \frac{P}{H^{2}} \le D) \land ((\exists a \in \mathbb{R},\; [a,\infty) \subseteq T) \Rightarrow D \le 2 \cdot P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the lower bound take a nonempty real time set T and H > 0. Short(S,g,H) says that each incompatible U contains an integer relation of coefficient sum nonzero modulo four and coefficient ℓ¹ length at most H. At each time retain exactly the coordinates with sine loss strictly below 1/H². If a short incompatible relation were supported there, its character on the orbit would be one and its value at the common quarter phase would be a nontrivial fourth root of unity, at distance at least √2 from one. The coordinate chord squared equals twice the sine loss. The character chord bound would therefore give a distance strictly below H · √2/H = √2. The orbit character, quarter character, and chord identity are supplied by Weighted Integer Relations. The retained set is compatible. Its complement costs at least P of the total weight and each deleted coordinate pays at least 1/H² of its weight.

For the upper bound assume that T contains an upper ray. For any compatible U, the orbit closure on the retained coordinates contains the common quarter phase on every upper ray. The retained score approaches its full weight by continuity. The omitted score is bounded below by minus the omitted weight, so the total loss is at most twice the omitted weight in the infimum. Minimizing over U gives the upper bound for any such T.

A finite H exists for every fixed finite frequency system. Choose one incompatible witness per incompatible subset and take the maximum of their lengths and 1. For actual ζ ordinates, the open question is quantitative control of H, such as a uniform bound or a bound in terms of the ordinate cutoff strong enough to yield an asymptotic conclusion.

**Theorem 1.2 (Quadratic separation for consecutive frequencies).**

$$P = \frac{1}{2} \land \left(\operatorname{Short}\left(S, g, H\right) \land \left((T \ne \emptyset \Rightarrow \frac{1}{H^{2} + 1} \le D) \land ((\exists a \in \mathbb{R},\; [a,\infty) \subseteq T) \Rightarrow (D \le 1 - \operatorname{cos}\left(\frac{\pi}{2 \cdot H}\right) \land \left(1 - \operatorname{cos}\left(\frac{\pi}{2 \cdot H}\right) \le \frac{\pi^{2}}{8 \cdot H^{2}} \land (n = 0 \Rightarrow D = \frac{1}{2})\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the frequencies (n,n + 1) with n a natural number and any equal positive weights w. The relation (n + 1,−n) has coefficient sum one and length H = 2n + 1. The full pair is incompatible, and the singleton {n + 1} is compatible, so the deleted fraction is 1/2. For n > 0 both singletons are compatible. At n = 0 the singleton {0} has a length-one incompatible relation. Thus the short relation condition holds at H for all n.

The weighted single-row character bound uses squared chord distance 2 from 1 to the quarter character i of this relation. Its weighted squared coefficient norm is ((n + 1)² + n²)/w, and the total weight is 2w. This gives D ≥ 1/(H² + 1) over all real times. Restricting the supremum to any nonempty T preserves the bound.

At time π/H the phases are π/2 ± π/(2H). Adding nonnegative integral multiples of 2π puts this time in any upper ray while preserving the score. The pointwise deficit there is 1 − cos(π/(2H)), at most π²/(8H²). At n = 0 the first frequency contributes zero. A translate of π/2 by a multiple of 2π in the ray makes the second sine equal one, giving D ≤ 1/2. The lower bound at H = 1 gives D = 1/2.

## References

- Truth anchor: `D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation`
- Truth anchor: `D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds`
- Dependency: [D5/S3/Fourier/WeightedIntegerRelations](WeightedIntegerRelations.md)
- Dependency: [D5/S3/Fourier/WeightedPhaseRelationLattice](WeightedPhaseRelationLattice.md)
