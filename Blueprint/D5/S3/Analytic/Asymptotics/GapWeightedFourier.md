# Fourier recovery on a mesh with vanishing gaps

## Abstract

Gap-weighted averages recover coefficients on a closed upper line.

**Theorem 1.1 (Coefficient recovery on a closed upper line).**

Lean statement: `D5/S3/Analytic/Asymptotics/GapWeightedFourier.tendsto_average_closed_strip_series`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GapWeightedFourier.tendsto_average_closed_strip_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let y be a strictly increasing real sequence tending to +∞ with gaps d(k)=y(k+1)−y(k) tending to zero. For M>0 the gap-weighted average of s is A(M)=∑_{k<M} d(k)s(k)/(y(M)−y(0)). Let a(i) and z(i) be complex families on an arbitrary index type with summable coefficient norms. Fix w in ℂ with Re(z(i))≤Re(w) for every i. If e(k) tends to zero in ℂ and s(k)=∑ᵢ a(i) exp(y(k)(z(i)−w))+e(k), then A(M) tends to the sum of a(i) over exactly the indices with z(i)=w.

The modes strictly below Re(w) decay. On the bounding line each nonzero frequency averages to zero by comparison with its integral over the mesh intervals. The mode at w is constant. The exponential factors are bounded by one once y is nonnegative, so absolute summability permits passage to the limit in the series. The average of the null error tends to zero.

**Theorem 1.2 (Two-sided excursions from a zero mean and a twisted limit).**

Lean statement: `D5/S3/Analytic/Asymptotics/GapWeightedFourier.frequently_two_signs_of_zero_mean`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GapWeightedFourier.frequently_two_signs_of_zero_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let y be a strictly increasing real sequence tending to +∞, let a(k) be real, and let u(k) be complex with norm one. Suppose the gap-weighted averages of a(k) tend to zero and those of a(k)u(k) tend to L. For each c≥0 with 2c<‖L‖, arbitrarily large indices satisfy a(k)>c and arbitrarily large indices satisfy a(k)<−c.

Under an eventual upper bound a(k)≤c, the quantity 2c−a(k)+2 max(a(k)−c,0) bounds |a(k)u(k)|. The correction has finite support and its gap-weighted average tends to zero. The triangle inequality and the zero mean then give ‖L‖≤2c. Applying the same argument to −a gives the lower excursions.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/GapWeightedFourier.frequently_two_signs_of_zero_mean`
- Truth anchor: `D5/S3/Analytic/Asymptotics/GapWeightedFourier.tendsto_average_closed_strip_series`
