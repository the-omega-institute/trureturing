# Sequential Hellinger Localization and Dichotomy

## Abstract

Predictable energy separates equivalence and singularity for full-history trajectory laws.

**Definition 1.1 (Predictable energy cut).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.energyCut`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.energyCut` (`✓ std3`).

*Citation.* Robert S. Liptser and Albert N. Shiryaev (2001). *Statistics of Random Processes*. DOI: [10.1007/978-3-662-13043-8](https://doi.org/10.1007/978-3-662-13043-8). URL: <https://doi.org/10.1007/978-3-662-13043-8>.

*Commentary.*

For any state type, real-valued energy sequence e, real threshold K and natural time n, energyCut(e,K,n) is the set of states at which the sum of e(i) for i less than n is at most K.

**Theorem 1.2 (Joint moment control and finite-energy convergence).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.common_energy_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.common_energy_localization` (`✓ std3`). ∎

*Citation.* Robert S. Liptser and Albert N. Shiryaev (2001). *Statistics of Random Processes*. DOI: [10.1007/978-3-662-13043-8](https://doi.org/10.1007/978-3-662-13043-8). URL: <https://doi.org/10.1007/978-3-662-13043-8>.

*Commentary.*

Let mu be a probability measure and F a filtration indexed by the natural numbers. The integrable energy e(n) is F(n)-measurable and takes values in [0,1]. The centered increment d(n) and nonnegative error y(n) are measurable at n+1. Each d(n) is square integrable, each y(n) is integrable, and the conditional mean of d(n) is zero. Their conditional second and first moments, respectively, are at most twice e(n). No uniform bound on d(n) or y(n) is required.

For every nonnegative integer K, retain increment n exactly when the sum of e(i) over i less than n is at most K. At every horizon, the second moment of the retained centered sum and the mean of the retained error sum are both at most 2(K+1). The extra one allows the final retained increment to cross K.

There is one full-measure set on which every path with summable energy has convergent natural-order centered partial sums and a summable nonnegative error sequence. The centered series is not asserted to converge absolutely. The argument first applies martingale convergence to each retained process, then intersects the countably many full-measure sets. A path with finite energy admits an integer level at which every original increment is retained.

**Theorem 1.3 (Strictly positive product limits).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.finite_energy_positive_product`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.finite_energy_positive_product` (`✓ std3`). ∎

*Citation.* Robert S. Liptser and Albert N. Shiryaev (2001). *Statistics of Random Processes*. DOI: [10.1007/978-3-662-13043-8](https://doi.org/10.1007/978-3-662-13043-8). URL: <https://doi.org/10.1007/978-3-662-13043-8>.

*Commentary.*

Let r(n) be strictly positive, square integrable and measurable at time n+1. Suppose its conditional mean is 1-e(n), and the conditional mean of (r(n)-1) squared is at most 2e(n), with predictable e(n) in [0,1]. Almost every path with summable energy has a strictly positive finite limit of the products of r(i) for i less than n.

Conditional variance bounds the squared centered increment by the same conditional error moment. Common energy localization therefore gives convergence of the centered sums and summability of (r(n)-1) squared. Subtracting the finite energy drift gives convergence of the sums of r(n)-1. The logarithmic remainder is eventually bounded by twice its square. Hence the natural-order logarithmic sums converge to a finite real number, whose exponential is the positive product limit. No uniform positive lower bound on the individual r(n) is imposed.

**Theorem 1.4 (Actual full-history likelihoods).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_likelihood_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_likelihood_limits` (`✓ std3`). ∎

*Citation.* Robert S. Liptser and Albert N. Shiryaev (2001). *Statistics of Random Processes*. DOI: [10.1007/978-3-662-13043-8](https://doi.org/10.1007/978-3-662-13043-8). URL: <https://doi.org/10.1007/978-3-662-13043-8>.

*Commentary.*

For a nonempty finite discrete alphabet, let p and q be strictly positive normalized rows indexed by finite histories. Let H(n,x) be the first n letters of x and let rho(h) be the sum over letters of the square root of p(h,a)q(h,a). Under trajectoryLaw(p), almost every path with summable 1-rho(H(n,x)) has a positive finite limit of the products of q(H(i,x),x(i))/p(H(i,x),x(i)) over i less than n.

The conditional distribution of the next letter is the row at the actual observed history. This identifies the two conditional root-likelihood moments used above. Each fixed-time increment has finite range, so it is square integrable even though no uniform bound across time is assumed. The initial-letter factor is included explicitly after applying the conditional argument to successor coordinates. Squaring the positive root-product limit gives the stated likelihood limit.

On paths whose nonnegative Hellinger energy is not summable, the likelihood converges to zero almost surely. Dividing each root increment by its strictly positive conditional affinity gives a nonnegative martingale with mean one. It has a finite limit almost surely. The product of the affinities is bounded by the exponential of minus accumulated energy, which tends to zero. Multiplying these two factors and restoring the initial coordinate proves the zero limit.

**Theorem 1.5 (Sequential Hellinger dichotomy).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_dichotomy` (`✓ std3`). ∎

*Citation.* Robert S. Liptser and Albert N. Shiryaev (2001). *Statistics of Random Processes*. DOI: [10.1007/978-3-662-13043-8](https://doi.org/10.1007/978-3-662-13043-8). URL: <https://doi.org/10.1007/978-3-662-13043-8>.

*Commentary.*

For a finite discrete alphabet with at least two letters, let p and q be strictly positive normalized rows at every finite history. Define C by finiteness of the extended nonnegative sum of 1-rho(H(n,x)). The restrictions of trajectoryLaw(p) and trajectoryLaw(q) to C are mutually absolutely continuous. There is no common positive lower bound assumption.

Write P and Q for the two laws. Under P+Q, the conditional expectations of the global Q-density at finite prefixes equal L/(1+L). Cylinder masses are obtained from the public frozen full-history trajectory theorem. The prefix filtration generates the full path sigma-algebra, so the conditional expectations converge to the global density. The positive finite likelihood limit on C makes that density positive P-almost everywhere on C, giving P restricted to C absolutely continuous with respect to Q restricted to C. Swapping the two rows repeats the argument under Q independently. No finite-prefix measurability is assumed of C.

The restrictions to the complement of C are mutually singular. Under P the likelihood tends to zero there; independently, under Q its reciprocal tends to zero. These limit properties give disjoint almost-everywhere filters and hence a common measurable separating set.

In addition, if the natural partial sums of negative log affinities tend to positive infinity almost surely under each of P and Q, the full laws are mutually singular. The reverse energy comparison uses the pinned summability theorem for log(1+u): summable 1-rho implies summable negative log rho, contradicting the stipulated divergence. The theorem does not assert a criterion for arbitrary regular kernels beyond these strictly positive finite-alphabet history rows.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.common_energy_localization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.energyCut`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.finite_energy_positive_product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_dichotomy`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.trajectory_hellinger_likelihood_limits`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum](HistoricalDepthBudgetJointExtremum.md)
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../../../TotalVariation/Bhattacharyya.md)
