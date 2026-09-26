# Countable Gaussian Quadratic Limit

## Abstract

Countable Gaussian quadratic rows have a Gaussian distributional limit when their maximal coefficient vanishes and their variance converges.

**Theorem 1.1 (Actual square-integrable sums and their limiting law).**

$$\forall Omega \in Type, Sigma \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega, Sigma\right), G \in {\mathbb{N}\to {\mathbb{N}\to {Omega\to \mathbb{R}}}}, a \in {\mathbb{N}\to {\mathbb{N}\to \mathbb{R}}}, v \in \mathbb{R}_{\ge0},\; \left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{HasLaw}\left(G(n,j), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{iIndepFun}\left(G(n), P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{Summable}\left((j:\mathbb{N}\mapsto a(n,j)^{2})\right)\right) \land \left(\operatorname{TendstoAtTop}\left((n:\mathbb{N}\mapsto \operatorname{sup}\left((j:\mathbb{N}\mapsto \left|a(n,j)\right|)\right)), 0\right) \land \operatorname{TendstoAtTop}\left((n:\mathbb{N}\mapsto \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(n,j)^{2})\right)), \frac{v}{2}\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists Q \in {\mathbb{N}\to \operatorname{Lp}\left(\mathbb{R}, 2, P\right)},\; \left(\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{MemLp}\left((omega:Omega\mapsto a(n,j) \cdot (G(n,j)(omega)^{2}-1)), 2, P\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{HasSum}\left((j:\mathbb{N}\mapsto \operatorname{toLp}\left(P, (omega:Omega\mapsto a(n,j) \cdot (G(n,j)(omega)^{2}-1))\right)), Q(n)\right)\right) \land \operatorname{TendstoInDistribution}\left((n:\mathbb{N}\mapsto \operatorname{representative}\left(Q(n)\right)), atTop, \operatorname{id}\left(\mathbb{R}\right), (n:\mathbb{N}\mapsto P), \operatorname{gaussianReal}\left(0, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.result` (`✓ std3`). ∎

*Citation.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let (Omega, Sigma, P) be any probability space, and let G(n,j) be real random variables indexed by two natural numbers. Every G(n,j) has the standard Gaussian law. For each fixed n, the entire countable family G(n,j) is independent. No independence between different rows is required.

The real coefficients a(n,j) are square summable in j for every n. Their supremum in absolute value tends to zero, and the sum of their squares tends to v/2, where v is any nonnegative real number. Set X(n,j)(omega)=a(n,j)(G(n,j)(omega)^2-1). Every X(n,j) belongs to L2(P). The notation toLp below means its equivalence class modulo almost-everywhere equality.

There exist Q(n) in L2(P) such that the series of these equivalence classes has sum Q(n). HasSum is convergence of finite-subset sums in the L2 norm; the rows need not have finite support. The actual measurable representatives of Q(n) converge in distribution to the centered Gaussian measure of variance v. In particular v=0 gives the point mass at zero.

Centered standard Gaussian squares have second moment two and are orthogonal within each independent row. The Hilbert-space series theorem therefore constructs the actual sums. For real t, the characteristic function of Q(n) is the exponential of the absolutely convergent sum of -it a(n,j)-Log(1-2it a(n,j))/2. Linear terms cancel inside each summand, before summation.

Writing M(n)=sup_j |a(n,j)| and S(n)=sum_j a(n,j)^2, the absolute value of the summed exponent plus t^2 S(n) is at most (8/3)|t|^3 M(n)S(n) whenever 2|t|M(n)<=1/2. This error tends to zero, and Levy's characteristic-function theorem gives the stated limit. The classical fixed-chaos Gaussian criterion is described by Nualart and Peccati, Theorem 1; the argument here uses characteristic functions directly.

This statement concerns scalar coefficient arrays. Applying it to a specified kernel or Wiener integral requires its actual spectral identification. It does not assert a process limit, mixing with old noise, or tightness.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.result`
