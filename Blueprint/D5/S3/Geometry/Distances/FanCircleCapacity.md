# Fan's moving three-point circle capacity

## Abstract

The exact measure-theoretic definitions in Fan's moving three-point circle capacity conjecture.

**Definition 1.1 (The moving three-point set).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.points`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.points` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

points(phi,psi) is the actual set of the three complex unit-circle points at polar angles psi, phi, and minus phi.

**Definition 1.2 (Positive-order energy).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.energy`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.energy` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

energy(r,K,mu) is the double integral of dist(x,y)^r against a ProbabilityMeasure on the actual subtype K. Zero singleton masses are not excluded.

**Definition 1.3 (Negative-exponent Riesz capacity).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.capacity`

*Formalization.* `D5/S3/Geometry/Distances/FanCircleCapacity.capacity` (`✓ std3`).

*Citation.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

capacity(r,K) is the reciprocal-r power of the supremum of energy over all probability measures on K, matching Fan's convention for negative exponent minus r.

**Theorem 1.4 (The moving three-point capacity is maximal at the isosceles endpoint).**

Lean statement: `D5/S3/Geometry/Distances/FanCircleCapacity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Distances/FanCircleCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Qiuling Fan (2026). *Riesz capacity ratios with negative exponents*. DOI: [10.48550/arXiv.2609.11186](https://doi.org/10.48550/arXiv.2609.11186). URL: <https://arxiv.org/abs/2609.11186v1>.

*Commentary.*

For every real r at least two and pi/2 < phi <= 2*pi/3, the capacity of the points at angles psi, phi and -phi is at most its value at psi = 2*pi - 3*phi whenever 0 <= psi <= 2*pi - 3*phi.

The proof represents every probability measure by all three singleton masses, including zero masses, and identifies the attained energy supremum with the classical three-point quadratic maximum. A unified positive-part formula is differentiable when the optimizer changes branch. Chord and cotangent identities, together with the real-power displacement inequality, make its derivative nonnegative throughout the motion. Monotonicity of the reciprocal-r power then gives the capacity inequality.

## References

- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.capacity`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.energy`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.points`
- Truth anchor: `D5/S3/Geometry/Distances/FanCircleCapacity.result`
