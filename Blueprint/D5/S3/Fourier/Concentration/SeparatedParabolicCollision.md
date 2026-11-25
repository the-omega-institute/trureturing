# Separated parabolic collision constructions

## Abstract

Finite separated parabolic weights attain the asymptotic collision variance coefficient.

**Theorem 1.1 (Exact finite mass, second moment and collision mass).**

$$0< n \Rightarrow \forall k\in S, 0\leq \operatorname{c}\left(k\right)\quad0< W, A = W, B = \frac{W \cdot (n^{2} - 1)}{5}, (E = \frac{W \cdot (4 \cdot n^{2} + 1)}{5} \Leftrightarrow 0\leq eta, (n = 1 \lor eta<1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.separated_parabolic_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural number n let S be the integer interval [−n,n]. The sites are x(k)=k and their weights are c(k)=n²−k². Write W=n(4n²−1)/3, A=Σ c(k), B=Σ c(k)k², with sums over S, and E=nearCollisionMass S x c η for arbitrary real resolution η.

The exact mass follows from `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.normalizer_formula`. The second moment follows from `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.lower_moment_difference`. The separation criterion `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.int_near_eq` ensures distinct integer sites differ by at least one, so the closed band at 0≤η<1 contains only the diagonal. Use c(k)²=n²c(k)−k²c(k) to evaluate the collision sum from the same moments.

At n=1 the center is the only positive weight, with zero second moment, and the formula holds for all nonnegative resolutions. At n≥2 and η≥1, the ordered pair (0,1) has strictly positive weight. The diagonal is still counted, so collision mass strictly exceeds the formula. Negative resolutions have zero collision mass.

**Theorem 1.2 (Attainment in the small relative resolution limit).**

$$0< L, \operatorname{Eventually}\left(0<\operatorname{eta}\left(n\right)<1\right), \operatorname{TendstoAtTop}\left(\operatorname{eta}\left(n\right), L\right) \Rightarrow \operatorname{TendstoAtTop}\left(\operatorname{T}\left(n\right), 0\right), \operatorname{TendstoAtTop}\left(\operatorname{C}\left(n\right), \frac{3}{5 \cdot \operatorname{sqrt}\left(5\right) \cdot L}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.parabolic_collision_ratio_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each natural index n let V(n)=(n²−1)/5, W(n)=n(4n²−1)/3, and E(n) the preceding construction’s collision mass at η(n). Assume η(n)→L>0 and eventually 0<η(n)<1. Write T(n)=η(n)/√V(n) and C(n)=E(n)√V(n)/(W(n)²η(n)).

Put t=1/n. The first ratio becomes √5 t η(n)/√(1−t²) and the second is (3/(5√5)) ((4+t²)/(4−t²))√(1−t²)/η(n). The finite identities apply eventually and the limiting denominators are nonzero. Continuity and t→0 prove both limits. Taking η(n)=n/(n+1) gives L=1 and attains the coefficient 3/(5√5).

The construction provides admissible finite witnesses for the limiting coefficient of the universal shifted-bin variance bound. It concerns arbitrary finite weighted data. Attainment subject to a fixed frequency-sum structure or to actual zeta ordinates requires additional arithmetic information.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.lower_moment_difference`
- Truth anchor: `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.normalizer_formula`
- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.int_near_eq`
- Truth anchor: `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.parabolic_collision_ratio_limit`
- Truth anchor: `D5/S3/Fourier/Concentration/SeparatedParabolicCollision.separated_parabolic_collision`
- Dependency: [D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation](../Asymptotics/LatticeSquareMomentActivation.md)
- Dependency: [D5/S3/Fourier/Concentration/DegreeTwoMomentWitness](DegreeTwoMomentWitness.md)
