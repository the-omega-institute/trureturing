# Sharp weighted interval estimates for BKM step profiles

## Abstract

Sharp weighted bounds and equality defects for qutrit BKM step profiles.

**Definition 1.1 (Interval mass).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass assigned to endpoints a and b is the difference of their inverses.

**Definition 1.2 (Interval coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient ab(b−a) extends continuously to equal endpoints and to a zero left endpoint.

**Theorem 1.3 (Weighted interval mass).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < a ≤ b this mass is the integral of dx/x² from a to b.

**Definition 1.4 (Integral of one level).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepIntegral`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scale the constant vector by the length of the interval.

**Definition 1.5 (Energy of one level).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepEnergy`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the squared norm of the level by the weighted interval mass.

**Theorem 1.6 (Integral formulas for one level).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.step_integrals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.step_integrals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < a ≤ b and a real normed vector space E with CompleteSpace E, stepIntegral agrees with the vector integral against dx and stepEnergy agrees with the integral of the squared norm against dx/x², both from a to b.

**Definition 1.7 (Three-interval coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the coefficients of the last two intervals of the mesh 0, x, x+y, x+y+z. The level on the first interval is zero.

**Theorem 1.8 (Cubic form of the coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient_eq_cubes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient_eq_cubes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the interval coefficients is one third of the difference between the cube of the total length and the sum of the cubes of the three lengths.

**Theorem 1.9 (Exact spacing deficit).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For mean length m, the difference from 8/27 times the cube of the total length is the sum of (x−m)²(x+2m), (y−m)²(y+2m), and (z−m)²(z+2m), divided by three.

**Theorem 1.10 (Optimal spacing).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative lengths and positive total length the coefficient is at most 8/27 times the cube of the total length, with equality exactly at equal spacing.

**Definition 1.11 (Mesh integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshIntegral`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the integrals of the two active levels.

**Definition 1.12 (Mesh energy).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshEnergy`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the weighted energies of the two active levels.

**Theorem 1.13 (Exact level deficit).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_energy_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_energy_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive lengths set p=x(x+y) and q=(x+y)(x+y+z). The mesh coefficient times the energy minus the squared integral is yz/(pq) times the squared norm of q·u−p·w.

**Theorem 1.14 (Sharp normalized profile bound).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For strictly positive lengths x, y, z with x+y+z=1 and levels u, w in a real inner-product space, the squared integral is at most 8/27 times the energy. At positive energy equality holds exactly at equal thirds with w=3u.

**Definition 1.15 (Coefficient of the first two jumps).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the larger of the coefficients for endpoints (s,c) and (t,c).

**Definition 1.16 (Coefficient of the remaining levels).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.tailCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.tailCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the coefficients for endpoints (c,min(d,T)) and (d,max(d,T)).

**Definition 1.17 (Common coefficient of a band).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.bandCoefficient`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.bandCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the head and tail coefficients using d=s+t and the common upper cutoff T.

**Theorem 1.18 (Tail at the unshifted cutoff).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_tail_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_tail_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the unshifted cutoff c₀=d−v with T=1−v, the tail coefficient is d(1−d)(1−2v) if d ≤ T and c₀T(1−d) if T < d.

**Theorem 1.19 (Uniform band coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_coefficient_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_coefficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set d=s+t, c=d−v−η, and T=1−v. If 0 < s ≤ t < c, d ≤ 1, v ≥ 0, and η ≥ 0, the band coefficient is bounded by the three-interval coefficient for lengths s, t, and 1−d, plus η. Equivalently, the bound is 8/27+η minus the exact spacing deficit for those lengths.

**Definition 1.20 (Correction for the two jumps).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction matches the mixed terms of the two head quadratic forms after the energy is multiplied by the head coefficient.

**Theorem 1.21 (Correction from the threshold gap).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection_eq_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection_eq_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < s ≤ t < c ≤ s+t the correction is 2(c−t)(t−s)/(stc), positive exactly when s<t.

**Definition 1.22 (Head integral).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headIntegral`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The levels on the first two active intervals are the first jump and the sum of both jumps.

**Definition 1.23 (Head energy).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headEnergy`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Weight the squared norms of the first jump and of the sum of both jumps by the masses of their intervals.

**Definition 1.24 (Integral with a row cutoff).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowIntegral`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the head integral and the two tail integrals, allowing a collapsed interval when the row ends before s+t.

**Definition 1.25 (Energy with a row cutoff).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowEnergy`

*Formalization.* `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the head energy and the two tail energies truncated at the row cutoff.

**Theorem 1.26 (Signed row bound).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For levels in a real inner-product space, assume 0 < s ≤ t < c ≤ d=s+t and c ≤ r ≤ T. The tail intervals are [c, min(d,r)] and [d, max(d,r)], so the final interval collapses when r ≤ d. Weighted Cauchy–Schwarz bounds the squared row integral by the band coefficient C times the row energy plus Cκ⟨a,b⟩, where κ is the jump correction and a, b are the first two jumps.

**Theorem 1.27 (Summing over a band).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_sum_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_sum_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set d=s+t, c=d−v−η, and T=1−v. Assume 0 < s ≤ t < c, d ≤ 1, v ≥ 0, and η ≥ 0, with c ≤ r ≤ T for every row in the finite sum. The sum of squared row integrals is bounded by (8/27+η) times the total row energy plus Cκ times the signed sum of real inner products of the first two jumps. For complex rows these inner products are the real parts of the complex pairings.

**Theorem 1.28 (Positive-energy saturation).**

Lean statement: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_equal_thirds_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_equal_thirds_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a real inner-product space, take any jumps a, b with P=a+b≠0. Set s=t=1/3, v=η=0, c=d=2/3, and r=T=1, with first tail level u=0 and final level w=3P. The first tail interval collapses and the mixed correction vanishes. The row energy is 6‖P‖² and the squared row integral is (16/9)‖P‖², giving equality at 8/27 times the energy.

For a faithful joint state τ with retained qutrit marginal ω, the physical energy loss G is the difference of the BKM power-integral pairings at ω and τ for K and its tensor lift. The numerator M is the squared Hilbert–Schmidt norm of the weighted commutator of the lifted K with log τ minus the lifted log ω. With L=log cond(τ) and LG/2=1, the physical reduction must identify the normalized row energies summing to one and give M/(L³G) as half the summed squared row integrals up to a vanishing error.

To apply the band bound, the energy-normalized resolvent rows must converge to the indicated step profiles with the first two jumps recovered from the adjacent retained transitions. The approximation must give a uniform error per unit row energy, allowing growing environment dimension. For a source band starting at v, c=s+t−v−ε−δ and T=1−v. With P the band source projection and U the destination projection onto joint log exponents at most s+t−ε, the required signed sum is the real part of the Hilbert–Schmidt pairing of (I−U)AP√τ and (I−U)BP√τ. Its asymptotic vanishing on the whole band, including rows ending before s+t, is a separate spectral estimate. The scalar factor 8/27 contributes 4/27 after the physical normalization.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.bandCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_coefficient_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_equal_thirds_attains`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_row_sum_sharp`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.band_tail_identity`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headEnergy`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.headIntegral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.intervalWeight_eq_integral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.jumpCorrection_eq_gap`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshCoefficient_eq_cubes`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshEnergy`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.meshIntegral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowEnergy`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.rowIntegral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepEnergy`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.stepIntegral`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.step_integrals`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.tailCoefficient`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_energy_deficit`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_deficit`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_mesh_sharp`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.three_interval_normalized`
