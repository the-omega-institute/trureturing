# Common shifted bins and a parabolic test

## Abstract

A shared shift and a quadratic lattice test give a variance lower bound for near-collision mass.

**Theorem 1.1 (A common shift with controlled squared moment).**

$$\exists u\quad0\leq u<1, \operatorname{B}\left(u\right)\leq Q + R$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ShiftedBinVariance.exists_shifted_squared_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index set S, let z and c have arbitrary real values. Write B(u) = Σ c(i)⌊z(i)+u⌋², Q = Σ c(i)z(i)² and R = Σ c(i){z(i)}(1−{z(i)}), with all sums over S and braces denoting fractional part.

For a single real z the shifted floor equals floor(z) on a subinterval of length 1−{z} and floor(z)+1 on the complementary subinterval. Integrating its square gives z²+{z}(1−{z}). The weighted integral is Q+R even for signed weights. Strict exceedance for every common shift in the half-open unit interval would contradict this integral.

**Theorem 1.2 (Variance lower bound from the clipped parabola).**

$$\forall i\in S, 0\leq \operatorname{c}\left(i\right)\quad0< eta, D\leq V \cdot W, 0< r, M\leq r^{2} \Rightarrow W^{2} \cdot (1 - \frac{M}{r^{2}})^{2} \le (\frac{16 \cdot r}{15} - \frac{1}{15 \cdot r^{3}}) \cdot E$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ShiftedBinVariance.collision_parabolic_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be finite, x and c real-valued, a and V real, and η positive. Write W = Σ c(i), D = Σ c(i)(x(i)−a)², M = V/η²+1/4, and E = nearCollisionMass S x c η, including ordered pairs at distance η. All sums defining W and D are over S. The radius r is a positive natural number.

The common shift applied to z(i) = (x(i)−a)/η gives integer bins b(i) with weighted second moment at most MW, since each rounding penalty is at most 1/4. Same-bin pairs have distance less than η. For q(k) = max(0,1−k²/r²), the weighted sum of q over those bins is at least W(1−M/r²). The square and fourth moment sums over the integer interval [−r,r] give Σ q(k)² = 16r/15−1/(15r³). Cauchy–Schwarz and the squared bin-mass lower bound from `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.sum_bin_mass_sq_le_nearCollisionMass` establish the assertion.

For degree-p frequency sums of nonnegative weights with positive total weight W₀ and centered variance V₀, the moment computation in `D5/S3/Fourier/Concentration/FiniteCollisionVariance.tailCollisionMass_lower_variance` gives total weight W₀ᵖ and centered variance pV₀. Substitute these values for W and V. The inequality gives a necessary collision budget at finite resolution. An arithmetic upper bound for actual zeta ordinates is an independent open step.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteCollisionVariance.tailCollisionMass_lower_variance`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.sum_bin_mass_sq_le_nearCollisionMass`
- Truth anchor: `D5/S3/Fourier/Concentration/ShiftedBinVariance.collision_parabolic_lower`
- Truth anchor: `D5/S3/Fourier/Concentration/ShiftedBinVariance.exists_shifted_squared_moment`
- Dependency: [D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation](../Asymptotics/LatticeSquareMomentActivation.md)
- Dependency: [D5/S3/Fourier/Concentration/FiniteCollisionVariance](FiniteCollisionVariance.md)
