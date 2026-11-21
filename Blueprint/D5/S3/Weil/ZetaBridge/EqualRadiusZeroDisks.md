# Equal-radius disks for a zeta zero to the right of one-half

## Abstract

Isolating a zeta zero at a controlled distance from a vertical line

**Theorem 1.1 (An occupied disk and an empty disk of the same radius).**

$$\forall z \in \mathbb{C},\; \forall s \in \mathbb{R},\; \forall e \in \mathbb{R},\; \left(\operatorname{zeta}\left(z\right) = 0 \land \left(2 < s \land \left(0 < e \land e < \operatorname{Re}\left(z\right) - \frac{1}{2}\right)\right)\right) \Rightarrow \left(\exists p \in \mathbb{C},\; \exists q \in \mathbb{C},\; \exists r \in \mathbb{R},\; \left(\operatorname{Re}\left(p\right) = s \land \operatorname{zeta}\left(q\right) = 0\right) \land \left(\left(0 < \operatorname{dist}\left(p, q\right) \land \left(\operatorname{dist}\left(p, q\right) < r \land r < s - \operatorname{Re}\left(z\right) + e\right)\right) \land \left(\left(\forall w \in \mathbb{C},\; \operatorname{dist}\left(s, w\right) \le r \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(w\right) \land \operatorname{zeta}\left(w\right) \ne 0\right)\right) \land \left(\forall w \in \mathbb{C},\; \operatorname{dist}\left(p, w\right) \le r \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(w\right) \land \left(\operatorname{zeta}\left(w\right) = 0 \Rightarrow w = q\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks.equal_radius_zero_disks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the statement s denotes σ, e denotes the loss δ, and q denotes the selected zero ρ. Write β for the real part of the given zero. For σ > 2 and 0 < δ < β − 1/2, the two centers have real part σ. The real center has no zeros in its closed disk. The other disk has one zero ρ at a strictly positive distance less than its radius r, where r < σ − β + δ. Every point of either closed disk has real part greater than one-half.

First compare the distance from σ to the nearest zero with σ − β + δ. If the latter is smaller, move the center to the ordinate of the given zero. Otherwise take a nearest zero to σ. It has real part greater than one-half and is nonreal by real-axis nonvanishing. Moving to its ordinate strictly shortens the distance.

For two distinct zeros, equality of distances from the vertical line occurs at most once. At equal ordinates their horizontal distances are distinct, and at distinct ordinates the tie is a single affine equation. The zeros are countable, so some nearby height avoids all ties. The other zeros form a closed set. Choosing the radius below their distance and below both preceding bounds gives the two closed disks.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks.equal_radius_zero_disks`
- Dependency: [D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation](AlternatingZetaContinuation.md)
