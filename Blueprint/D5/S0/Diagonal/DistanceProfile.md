# Diagonal Distance Profiles

## Abstract

Diagonal Hamming-distance profiles and lower tails have exact finite counts.

**Theorem 1.1 (Exact distance profiles factor rowwise).**

$$\operatorname{card}\left(\operatorname{distanceProfileFiber}\left(f, r\right)\right) = \operatorname{productRows}\left(\operatorname{rowDistanceCount}\left(f, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/DistanceProfile.distance_profile_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each row, the diagonal entry contributes either zero or one to the distance. The remaining coordinates form a finite Hamming sphere, whose choice count is a binomial coefficient times a power of one fewer than the value-set cardinality. Summing the fixed and nonfixed diagonal cases gives the explicit rowDistanceCount, and the rows then multiply independently.

**Theorem 1.2 (Common distance lower tails are row powers).**

$$\operatorname{card}\left(\operatorname{minimumDistanceListings}\left(f, r\right)\right) = \operatorname{sum}\left(\operatorname{rowDistanceCount}\left(f, j\right), j, r, \operatorname{card}\left(A\right)\right)^{\operatorname{card}\left(A\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/DistanceProfile.min_distance_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every row distance lies between zero and the address cardinality. Summing the exact row counts over the closed lower-tail interval and then multiplying over all rows yields the stated finite count.

**Theorem 1.3 (Positive distance recovers the escape count).**

$$\operatorname{card}\left(\operatorname{positiveDistanceListings}\left(f\right)\right) = \left(\operatorname{card}\left(Y\right)^{\operatorname{card}\left(A\right)} - \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)\right)^{\operatorname{card}\left(A\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/DistanceProfile.min_distance_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A listing is escaped exactly when every row has positive distance from the twisted diagonal. The lower-tail formula at one is identified with the previously frozen exact escape count through that equivalence, without recounting escaped listings.

## References

- Truth anchor: `D5/S0/Diagonal/DistanceProfile.min_distance_tail`
- Truth anchor: `D5/S0/Diagonal/DistanceProfile.distance_profile_card`
- Truth anchor: `D5/S0/Diagonal/DistanceProfile.min_distance_one`
- Dependency: [D5/S0/Diagonal/EscapeCount](EscapeCount.md)
