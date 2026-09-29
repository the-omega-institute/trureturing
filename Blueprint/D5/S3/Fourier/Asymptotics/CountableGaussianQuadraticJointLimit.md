# Joint Gaussian Quadratic Limit

## Abstract

Countable Gaussian quadratic sums converge jointly with fixed old Gaussian coordinates to an independent Gaussian limit.

**Theorem 1.1 (Actual sums and the product limiting law).**

$$\forall Omega \in Type, Sigma \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega, Sigma\right), d \in \mathbb{N}, X \in {Omega\to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)}, G \in {\mathbb{N}\to {\mathbb{N}\to {Omega\to \mathbb{R}}}}, a \in {\mathbb{N}\to {\mathbb{N}\to \mathbb{R}}}, v \in \mathbb{R}_{\ge0},\; \left(\left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\operatorname{AEMeasurable}\left(X, P\right) \land \left(\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{HasGaussianLaw}\left((omega:Omega\mapsto \operatorname{Pair}\left(X(omega), (j:\operatorname{Fin}\left(k\right)\mapsto G(n,j)(omega))\right)), P\right)\right)\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{HasLaw}\left(G(n,j), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{iIndepFun}\left(G(n), P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{Summable}\left((j:\mathbb{N}\mapsto a(n,j)^{2})\right)\right) \land \left(\operatorname{TendstoAtTop}\left((n:\mathbb{N}\mapsto \operatorname{sup}\left((j:\mathbb{N}\mapsto \left|a(n,j)\right|)\right)), 0\right) \land \operatorname{TendstoAtTop}\left((n:\mathbb{N}\mapsto \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(n,j)^{2})\right)), \frac{v}{2}\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists Q \in {\mathbb{N}\to \operatorname{Lp}\left(\mathbb{R}, 2, P\right)},\; \left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{MemLp}\left((omega:Omega\mapsto a(n,j) \cdot (G(n,j)(omega)^{2}-1)), 2, P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{HasSum}\left((j:\mathbb{N}\mapsto \operatorname{toLp}\left(P, (omega:Omega\mapsto a(n,j) \cdot (G(n,j)(omega)^{2}-1))\right)), Q(n)\right)\right) \land \operatorname{TendstoInDistribution}\left((n:\mathbb{N}\mapsto (omega:Omega\mapsto \operatorname{Pair}\left(X(omega), \operatorname{representative}\left(Q(n)\right)(omega)\right))), atTop, \operatorname{id}\left(\operatorname{Product}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \mathbb{R}\right)\right), (n:\mathbb{N}\mapsto P), \operatorname{ProductMeasure}\left(\operatorname{map}\left(P, X\right), \operatorname{gaussianReal}\left(0, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticJointLimit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

On any probability space, let X be a fixed almost-everywhere measurable vector in a finite-dimensional real Euclidean space. Its mean is arbitrary and its covariance may be singular. Each countable row G(n,j) consists of independent standard real Gaussian variables. Rows may be coupled arbitrarily. For every n and N, the actual joint law of X and the first N coordinates of row n is Gaussian. Independence between X and any row is not assumed.

The real coefficients a(n,j) are square summable in each row. Their supremum in absolute value tends to zero and their sum of squares tends to v/2 for a nonnegative variance v. Every centered weighted square belongs to L2. The series has an actual HasSum in L2, and the pair consisting of X and the representative of its sum Q(n) converges in distribution to the product of the law of X and the centered Gaussian law of variance v.

The result includes v=0, zero-dimensional X, infinite rows, negative coefficients, nonzero row/old correlations, and singular old covariance. The old vector is fixed as n varies. The rows do not need a common chosen noise basis.

For each real linear functional of X, finite Gaussian regression yields an independent residual and bounds the sum of squared regression coefficients by the fixed old variance. The mixed characteristic-function defect is controlled by the largest quadratic coefficient. L2 convergence passes this estimate to the countable sums. Combining the vanishing defect with the scalar Gaussian limit yields the product characteristic function, and the finite-dimensional Levy theorem gives weak convergence.

This is a joint finite-dimensional distribution theorem. A process mixing limit additionally requires the actual kernel representation, operator estimate, tightness, and measurable-cylinder approximation.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticJointLimit.result`
- Dependency: [D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit](CountableGaussianQuadraticLimit.md)
- Dependency: [D5/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect](GaussianQuadraticMixedDefect.md)
