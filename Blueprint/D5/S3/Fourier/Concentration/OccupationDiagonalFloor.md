# Dimension-sensitive occupation floor

## Abstract

Multinomial occupation concentration gives lower bounds on the diagonal mass and Fejer moments.

Let J be a finite index type with a distinguished index j0, nonnegative real weights w of total mass one, and a natural degree p. Write c(m) for the multinomial weight of an occupation m with total p. Let D be the sum of c(m)^2 over all such occupations. For each j different from j0 choose a positive radius r(j). Define V as the sum over these coordinates of p w(j)(1-w(j))/r(j)^2 and B as the product of 1+2r(j).

**Theorem 1.1 (An anisotropic occupation bound).**

$$\operatorname{max}\left(0, 1 - V\right)^{2} \le B \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/OccupationDiagonalFloor.occupation_diagonal_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the centered multinomial second moment to the coordinate indicator minus its mean w(j). The weighted squared deviation of the occupation count is p w(j)(1-w(j)). Consequently the weighted sum of squared deviations divided by the squared radii has expectation V. Occupations with the sum of the scaled squared deviations at most one have total mass at least max(0,1-V). In each coordinate their integer counts lie in the interval from p w(j)-r(j) to p w(j)+r(j), which contains at most 1+2r(j) integers. Projection away from j0 is injective on occupations with fixed total p. Cauchy-Schwarz gives the squared retained mass bounded above by B D.

**Theorem 1.2 (The floor in the actual Fejer moment).**

$$\operatorname{max}\left(0, 1 - V\right)^{2} \le B \cdot M$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/OccupationDiagonalFloor.fejer_occupation_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real frequencies g on J and every positive resolution eta let M be the whole-line integral of K_eta(t) |S(t)|^(2p), where S(t) is the weighted complex Fourier score. The triangular Fourier identity represents M as a finite sum of nonnegative terms. Its diagonal terms equal the individual c(m)^2, because the triangular function at zero is one. Thus M is at least D and obeys the same floor.

For positive p, choose all radii equal to sqrt(2p). The sum of the single-coordinate variances divided by 2p is at most one half, and B=(1+2sqrt(2p))^(card(J)-1). Hence M is at least one quarter divided by B. With a fixed finite support of d+1 indices, a fixed positive variance, and a resolution tending to zero faster than p^(-(d-1)/2), the Gaussian-normalized whole-line moment diverges. The lower bound leaves the actual varying zeta-ordinate support and arithmetic noncentral estimates open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/OccupationDiagonalFloor.fejer_occupation_floor`
- Truth anchor: `D5/S3/Fourier/Concentration/OccupationDiagonalFloor.occupation_diagonal_lower`
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionVariance](FejerCollisionVariance.md)
- Dependency: [D5/S3/Fourier/Concentration/FiniteCollisionVariance](FiniteCollisionVariance.md)
