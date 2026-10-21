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

The stronger gaussian_observation_law_complete API retains every conjunct of gaussian_observation_law and additionally proves outer integrability of y mapped to physicalFreeEnergy beta (posteriorKernel M beta tau y) under the actual dataLaw M beta tau. Thus the outer expectation is justified before centering by the finite prior free energy; no integrability assumption on an estimator is introduced. The original theorem is the first projection of this complete result.

The exposed translate_gaussian, precision_posDef, translatedKernel_apply, action_apply, action_adjoint, transpose_pairing and map_gaussian helpers identify the same affine Gaussian measures, matrix actions and actual posterior kernels used in the proof. They organize existing Gaussian and linear-algebra arguments and carry no independent novelty claim. The probability and Markov instances are structural support for these laws.

For the original trajectory experiment substitute n=p=Fin d, M=M_T from any chosen orthonormal basis of the actual L2 trajectory image, sigma=sigma(T), and tau=1/v(T), where v(T)=sigma(T)^2>0. On the original probability space, independence of X and xi with their stated Gaussian laws identifies the pushforward law of (Y_T,X), not just its covariance, with jointLaw M_T beta tau. The outer-integrability result then applies to that same data marginal. Tonelli gives the risk identity for all measurable estimators, including infinite-risk competitors. The existing SpectralNoiseAsymptotics application gives all-real-alpha information including occupied thresholds, risk away only from occupied thresholds, and the exact recovery equivalence for arbitrary positive variance schedules without regularity assumptions. Its separate fixed-eta clause has coefficient trace(C transpose C)/(2 beta eta) and a quadratic remainder without observability. These statements concern conditional probability descriptions and do not settle the separate physical implementation or open operator-window alternatives.

Same-delivery information-escape audits for the newly exposed API theorems remain unfinished; see https://github.com/the-omega-institute/trureturing/issues/20111. Existing audit sources are preserved. Neither compilation of candidate registrations nor this issue is declared_validated evidence.

For an independent realization, let X and xi be measurable random vectors on any probability space, with laws N(0,beta inverse I) and N(0,I), respectively, and set Y=MX+sigma xi. Scaling gives sigma xi the covariance sigma squared I and preserves its independence from X. Thus the law of (X,sigma xi) is the product of those two Gaussian laws. Pushing this product forward by (x,n) mapped to (Mx+n,x) identifies the full law of (Y,X) with jointLaw M beta tau in gaussian_observation_law. Consequently its posterior kernel, data marginal and KL mutual information are those of this same Y. This argument uses beta>0 and sigma squared>0 and allows either sign of sigma.

For every measurable estimator a, define R(a) as the nonnegative integral of half the squared norm of X-a(Y), with values in the extended nonnegative reals. Under the posterior N(Ay,Sigma), the conditional integral is trace(Sigma)/2 plus half the squared norm of Ay-a(y): each coordinate contributes its variance and squared displacement of its mean. Apply Tonelli to the joint disintegration to obtain R(a)=trace(Sigma)/2 plus the nonnegative integral under mu of half the squared norm of Ay-a(y). This identity includes infinite-risk competitors and requires no integrability assumption on a. The measurable linear estimator y mapped to Ay has zero excess term and finite risk trace(Sigma)/2, so it attains the infimum over all measurable estimators.

The Gaussian moment and entropy integrability in the free-energy argument also make y mapped to F(beta,K(y)) integrable under mu. Since mu has total mass one, subtracting the constant prior free energy inside this integral gives the centered identity: the expectation of F(beta,K(Y))-F(beta,prior) is beta inverse times the same mutual information. This is the free energy of the conditional probability description; a physical measurement, feedback or erasure protocol requires its own model.

For known dynamics with B transpose equal to -B, put F_t=exp(tB). The adjoint of F_t is exp(-tB), and their product in either order is the identity, so F_t preserves Euclidean distances. For every measurable future estimator a and every t>=0, the loss between F_t X and a(Y) equals the loss between X and F_t inverse applied to a(Y), pointwise. Composition with this continuous inverse is a bijection on measurable estimators. Hence the future infimum is again trace(Sigma)/2, attained by F_t A Y, with the same data and every measurable competitor, including those of infinite risk.

## References

- Truth anchor: `D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law`
