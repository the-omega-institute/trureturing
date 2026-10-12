# Supermodularity of the four-rate envelope

## Abstract

The exact four-rate min-envelope satisfies the lattice inequality on its full closed real cube.

Coordinates are indexed by Fin(4), from zero to three, and take arbitrary real values. Infimum and supremum of vectors are pointwise minimum and maximum. The lower and upper rate bounds are 2/9 and 6/25. The threshold T is 16/729, the tail bound q is 1944/390625, the slope kappa is 1116529/806625, and the intercept zeta is -151298/268875.

**Definition 1.1 (The two-branch upper rate).**

$$\forall X \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; \operatorname{ceilingRate}\left(X\right)=\operatorname{min}\left(\frac{\frac{16}{729}}{\operatorname{coordinate}\left(X, 1\right)*\operatorname{coordinate}\left(X, 2\right)}, \frac{\frac{1944}{390625}}{\operatorname{coordinate}\left(X, 1\right)*\operatorname{coordinate}\left(X, 2\right)*\operatorname{coordinate}\left(X, 3\right)}\right)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.ceilingRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two values agree when coordinate three equals h=q/T=177147/781250, which lies strictly between the two rate bounds. For X in the closed cube [2/9,6/25]^4, the minimum uses the threshold branch below h and the tail branch above h.

**Definition 1.2 (The scalar envelope).**

$$\forall X \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; \operatorname{envelope}\left(X\right)=\operatorname{ceilingRate}\left(X\right)*(1+\operatorname{coordinate}\left(X, 1\right)+\operatorname{coordinate}\left(X, 1\right)*\operatorname{coordinate}\left(X, 2\right))-\frac{\frac{1116529}{806625}*\operatorname{ceilingRate}\left(X\right)*(1+\operatorname{coordinate}\left(X, 0\right))}{\operatorname{ceilingRate}\left(X\right)+\operatorname{coordinate}\left(X, 0\right)}-(-\frac{151298}{268875})$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.envelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational correction uses coordinate zero and the same upper rate.

**Definition 1.3 (The adjusted envelope).**

$$\forall X \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; \operatorname{H}\left(X\right)=\operatorname{envelope}\left(X\right)-\operatorname{coordinate}\left(X, 0\right)*\operatorname{coordinate}\left(X, 1\right)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjustment subtracts the product of coordinates zero and one.

**Definition 1.4 (The full closed cube).**

$$\forall X \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; \operatorname{InCube}\left(X\right)\iff\forall i \in \operatorname{Fin}\left(4\right),\; \frac{2}{9}\le\operatorname{coordinate}\left(X, i\right)\land\operatorname{coordinate}\left(X, i\right)\le\frac{6}{25}$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.InCube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate varies independently over the closed interval, including both endpoints.

**Theorem 1.5 (The global lattice inequality).**

$$\forall X \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; \forall Y \in \operatorname{Fin}\left(4\right)\longrightarrow Real,\; (\operatorname{InCube}\left(X\right)\land\operatorname{InCube}\left(Y\right))\Rightarrow\operatorname{H}\left(X\right)+\operatorname{H}\left(Y\right)\le\operatorname{H}\left(\operatorname{inf}\left(X, Y\right)\right)+\operatorname{H}\left(\operatorname{sup}\left(X, Y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.four_rate_supermodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replace coordinate three by max(h,x3). This transformation preserves pointwise minimum and maximum and sends the cube into itself. The upper rate then equals q/(x1 x2 max(h,x3)), so one rational formula handles both branches and their common seam.

For the smooth formula, all six coordinate rectangles have nonnegative slack. The rational contribution for coordinates zero and one dominates the product of their increments. For zero paired with either remaining coordinate it is nonnegative; for two distinct active coordinates its factored numerator is nonnegative because x0 x1 x2 x3/q is at most 2/3. Positive reciprocal terms also have nonnegative rectangle slack. The pair of coordinates zero and one absorbs the subtracted product.

Telescoping these pairwise inequalities proves the vector lattice inequality. Equal coordinates and closed edges are included. The statement supplies a scalar inequality; it asserts no representation, rigidity, exclusion of a zero level, compactness or positive attained minimum for probability flows.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.H`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.InCube`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.ceilingRate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.envelope`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourRateSupermodularity.four_rate_supermodular`
