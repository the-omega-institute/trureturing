# Exact support thresholds on the integer lattice

## Abstract

A second-moment budget on the integer lattice determines the support of the unique squared-mass minimizer.

**Theorem 1.1 (The budgets for one radius interval).**

$$\forall n,m\quad0 < n\quad\longrightarrow\quad\frac{n^{2} - 1}{5} \le m \le \frac{n \cdot \left(n + 2\right)}{5} \Leftrightarrow \exists! (t,Z,w)\quad\operatorname{Activation}\left(m, n, t, Z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer_on_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n is a positive integer and m is real. Activation(m,n,t,Z,w) requires n² ≤ t ≤ (n+1)² and Z = Σ_{|j|≤n}(t−j²) > 0. The law w on the integers is max(0,t−j²)/Z. It is nonnegative with convergent sums giving mass one and second moment m. Each budget endpoint occurs exactly at the corresponding endpoint for t. At t=n² the support is [−(n−1),n−1] in the integers. For n²<t≤(n+1)² the support is [−n,n]. At m=0 the law is the point mass at zero.

For every nonnegative competitor v with mass one and convergent second moment s, its squared mass minus that of w equals Σ_j(v(j)−w(j))² + 2(m−s)/Z plus the summable nonnegative correction 2 Σ_j max(0,j²−t)v(j)/Z. If s≤m and v differs from w, its squared mass is strictly greater than that of w.

Finite sums of squares and fourth powers give the normalized second moment at both endpoints. The denominator stays positive and the moment varies continuously, so every intermediate budget is attained. To prove the comparison, expand the squared masses and split the cross term into the affine function (t−j²)/Z and its correction outside the support.

**Theorem 1.2 (Coverage of all nonnegative budgets).**

$$\forall m\quad0 \le m \Leftrightarrow \exists! (n,t,Z,w)\quad0 < n, \frac{n^{2} - 1}{5} \le m < \frac{n \cdot \left(n + 2\right)}{5}, \operatorname{Activation}\left(m, n, t, Z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m≥0 choose n as the floor of sqrt(5m+1). The floor gives a positive index whose lower threshold is at most m and whose upper threshold is strictly greater. Conversely a nonnegative law has nonnegative second moment. The half-open intervals are disjoint. At a shared endpoint the closed intervals select the same law, radius parameter and normalizer. The laws agree by strict comparison. Since t≥1, the values w(0)=t/Z and w(0)−w(1)=1/Z then identify Z and t.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer`
- Truth anchor: `D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer_on_interval`
