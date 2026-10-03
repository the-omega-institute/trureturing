# Gaussian observation laws and conditional information

## Abstract

Gaussian observation laws and conditional information

**Theorem 1.1 (Posterior disintegration, likelihood and conditional free energy).**

$$\begin{gathered}P=\operatorname{compProd}(\mu, K), \ell\in L^{1}(P), \operatorname{I}(X, Y)<\infty\\{}\operatorname{I}(X, Y)=\int\ell dP=\frac{\log\operatorname{det}(\beta^{-1}I)-\log\operatorname{det}(\Sigma)}{2}\\{}\operatorname{I}(X, Y)=\frac{1}{2}\log\operatorname{det}(I+\frac{\tau}{\beta}M^{T}M)\\{}\int\operatorname{F}(\beta, \operatorname{K}(y)) d\mu-\operatorname{F}(\beta, \operatorname{N}(0, \beta^{-1}I))=\beta^{-1}\operatorname{I}(X, Y)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n and p be arbitrary finite index sets, including empty sets, and let M be any real p by n matrix. Let beta be positive and let sigma be any real number with sigma squared positive. Put tau equal to the inverse of sigma squared. The input is the centered Gaussian law on the Euclidean space indexed by n plus p, with block diagonal covariance beta inverse times the identity on n and tau inverse times the identity on p. Its signal and noise coordinate maps have those respective centered Gaussian laws and are independent. Write X and N for these coordinates, Y=MX+N, P for the actual pushforward law of (Y,X), and mu for the actual law of Y.

Define Q=beta I+tau M transpose M, Sigma=Q inverse, and A=tau Sigma M transpose. The posterior kernel K(y) is the pushforward of the centered Gaussian law with covariance Sigma along x mapped to Ay+x. It disintegrates the same actual joint law: P=mu tensor K. No injectivity or rank condition is imposed on M.

Let ell be the log likelihood ratio obtained from the actual Radon–Nikodym derivative of P with respect to the product of its marginals. It is integrable under P. The ENNReal Kullback–Leibler divergence I is finite before its conversion to a real number. Its real value is both the integral of ell and one half the difference between the log determinant of beta inverse I and the log determinant of Sigma. The display gives the equivalent observation-Gramian formula.

For a probability law nu on the signal space, h(nu) is minus the integral under nu of the logarithm of its Radon–Nikodym density with respect to Euclidean volume. Define F(beta,nu) as the expected squared Euclidean norm divided by two, minus beta inverse times h(nu). The mean posterior value of this same functional, minus its prior value, equals beta inverse times I. All laws, densities and likelihoods refer to the same joint experiment. A negative sigma is allowed, and empty determinants equal one.

The precision is positive definite because its prior term is positive definite and its observation term is positive semidefinite. The innovation X-AY has covariance Sigma and zero cross covariance with Y, hence is independent of Y; reconstructing X gives the posterior disintegration. Integrable products of the scalar standard Gaussian density give the independent Gaussian density, and affine Haar transport with the absolute inverse determinant gives the nondegenerate density. Its Radon–Nikodym ratio yields the actual likelihood. Gaussian second moments prove logarithmic integrability, and integration gives the determinant identity. Mean conditional energy equals prior energy, so the entropy difference also gives the conditional free-energy identity.

## References

- Truth anchor: `D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law`
