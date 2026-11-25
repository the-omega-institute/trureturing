# Separated parabolic collision constructions

## Abstract

Finite separated parabolic weights attain the asymptotic collision variance coefficient.

**Theorem 1.1 (Exact finite mass, second moment and collision mass).**

$$0< n, 0\leq eta<1 \Rightarrow \forall k\in S, 0\leq \operatorname{c}\left(k\right)\quad0< W, A = W, B = \frac{W \cdot (n^{2} - 1)}{5}, E = \frac{W \cdot (4 \cdot n^{2} + 1)}{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.separated_parabolic_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural number n let S be the integer interval [−n,n]. The sites are x(k)=k and their weights are c(k)=n²−k². Write W=n(4n²−1)/3, A=Σ c(k), B=Σ c(k)k², with sums over S, and E=nearCollisionMass S x c η for real resolution η in [0,1).

Exact lattice normalization and the lower endpoint moment identity in `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer_on_interval` give the mass and second moment. Distinct integer sites differ by at least one, so the closed band at resolution η contains only the diagonal. Use c(k)²=n²c(k)−k²c(k) to evaluate the collision sum from the same moments.

At n=1 the center is the only positive weight, with zero second moment. For n≥2 the variance about zero is positive. The closed radius η=1 can admit adjacent positive-weight pairs, so the strict bound on η is material.

**Theorem 1.2 (Attainment in the small relative resolution limit).**

$$\operatorname{TendstoAtTop}\left(\operatorname{T}\left(n\right), 0\right), \operatorname{TendstoAtTop}\left(\operatorname{C}\left(n\right), \frac{3}{5 \cdot \operatorname{sqrt}\left(5\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.parabolic_collision_ratio_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each natural index n let V(n)=(n²−1)/5, η(n)=n/(n+1), W(n)=n(4n²−1)/3, and E(n) the preceding construction's collision mass at η(n). The data are admissible for every n≥2. Write T(n)=η(n)/√V(n) and C(n)=E(n)√V(n)/(W(n)²η(n)).

Put t=1/n. The first ratio becomes √5 t/((1+t)√(1−t²)) and the second is (3/(5√5)) ((4+t²)/(4−t²))√(1−t²)(1+t). The finite identities apply for n≥2 and every denominator used in the limit is nonzero at t=0. Continuity and t→0 prove both limits.

The construction provides admissible finite witnesses for the limiting coefficient of the universal shifted-bin variance bound. It concerns arbitrary finite weighted data. Attainment subject to a fixed frequency-sum structure or to actual zeta ordinates requires additional arithmetic information.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer_on_interval`
- Truth anchor: `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.parabolic_collision_ratio_limit`
- Truth anchor: `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.separated_parabolic_collision`
- Dependency: [D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation](../Asymptotics/LatticeSquareMomentActivation.md)
- Dependency: [D5/S3/Fourier/Concentration/DegreeTwoMomentWitness](DegreeTwoMomentWitness.md)
