# Actual graph weighted balance

## Abstract

Actual graph weighted balance

Symmetry of the actual graph interchanges the neighbor sums. Any integer weight satisfying the displayed local eigenvector identity annihilates the selected-degree balance of every actual finite set. This general summation lemma is used with the original periodic weight table, without a spectral assumption.

**Definition 1.1 (neighborSum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.neighborSum`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.neighborSum` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighborSum (weight : V → ℤ) (v : V) : ℤ.

**Theorem 1.2 (annihilate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.annihilate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.annihilate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem annihilate (weight : V → ℤ) (c : ℤ) (hweight : ∀ v, neighborSum G weight v + c * weight v = 0) (D : Finset V) : ∑ v : V, weight v * ((selectedDegree G D v : ℤ) + c * (if v ∈ D then 1 else 0)) = 0.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.annihilate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.neighborSum`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
