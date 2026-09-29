# Gaussian Quadratic Mixed Defect

## Abstract

A uniform bound quantifies the dependence between Gaussian linear coordinates and diagonal quadratic sums.

**Theorem 1.1 (Correlated old coordinates and a finite Gaussian row).**

$$\forall Omega \in Type, Sigma \in \operatorname{MeasurableSpace}\left(Omega\right), J \in FiniteType, P \in \operatorname{Measure}\left(Omega, Sigma\right), G \in {J\to {Omega\to \mathbb{R}}}, Y \in {Omega\to \mathbb{R}}, a \in {J\to \mathbb{R}}, M \in \mathbb{R},\; \left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\left(\forall j \in J,\; \operatorname{HasLaw}\left(G(j), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right) \land \left(\operatorname{iIndepFun}\left(G, P\right) \land \left(\operatorname{HasGaussianLaw}\left((omega:Omega\mapsto \operatorname{Pair}\left(Y(omega), (j:J\mapsto G(j)(omega))\right)), P\right) \land \left(0\le M \land \left(\forall j \in J,\; \left|a(j)\right|\le M\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{norm}\left({\operatorname{charFun}\left(\operatorname{map}\left(P, (omega:Omega\mapsto Y(omega)+\operatorname{sum}\left((j:J\mapsto a(j) \cdot {G(j)(omega)^{2}-1})\right))\right), 1\right)-\operatorname{charFun}\left(\operatorname{map}\left(P, Y\right), 1\right) \cdot \operatorname{charFun}\left(\operatorname{map}\left(P, (omega:Omega\mapsto \operatorname{sum}\left((j:J\mapsto a(j) \cdot {G(j)(omega)^{2}-1})\right))\right), 1\right)}\right)\le M \cdot \operatorname{variance}\left(Y, P\right) \cdot \operatorname{exp}\left(M \cdot \operatorname{variance}\left(Y, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a probability measure on an arbitrary measurable space. Let G(j) be a finite independent family of standard real Gaussian variables. Let Y be any real random variable such that the actual pair of Y and the whole row G is jointly Gaussian. The mean of Y is unrestricted, and its variance may vanish. No independence of Y and G is assumed.

For arbitrary signed coefficients a(j) with absolute value at most a nonnegative M, set Q equal to the sum of a(j)(G(j)^2-1). The difference between the characteristic function of Y+Q at one and the product of the characteristic functions of Y and Q at one has norm at most M Var(Y) exp(M Var(Y)). The estimate is independent of the number of row coordinates and includes the empty row.

Regression uses b(j)=Cov(Y,G(j)). Its residual Y minus the sum of b(j)G(j) is jointly Gaussian and uncorrelated with the row, hence independent of it. Its nonnegative variance implies that the sum of b(j)^2 is at most Var(Y). The linear-plus-quadratic Gaussian integral and the exponential remainder bound then give the displayed estimate.

Scaling a by a test frequency gives the mixed characteristic-function estimate at that frequency. Passing the bound through L2 truncations allows countable quadratic sums; the finite estimate itself does not assert convergence in distribution.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect.result`
