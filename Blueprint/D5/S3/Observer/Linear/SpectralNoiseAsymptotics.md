# Noise scales for finite power-controlled spectra

## Abstract

Noise scales for finite power-controlled spectra

**Theorem 1.1 (Information growth and complete recovery).**

$$\operatorname{powerBounds}(q, \lambda, c, C) \land \beta>0 \Rightarrow (\begin{gathered}\forall \alpha\in\mathbb{R}, \operatorname{I}(\alpha, T)-\frac{1}{2}\sum_{i=0}^{n} \operatorname{max}(\alpha-\operatorname{q}(i), 0) \log(\frac{1}{T})=\operatorname{O}(1)\\{}\forall \varepsilon:\mathbb{R}\to\mathbb{R}, (\forall T>0, \varepsilon(T)>0) \Rightarrow (\lim_{T\to0^{+}}\operatorname{R}(\varepsilon, T)=0 \iff \varepsilon(T)=\operatorname{o}(T^{\operatorname{q}(n)}))\\{}\forall \alpha\in\mathbb{R}, (\forall i\in\operatorname{Fin}(n+1), \alpha\neq\operatorname{q}(i)) \Rightarrow \lim_{T\to0^{+}}\operatorname{R}(\alpha, T)=\frac{\operatorname{card}(\{i: \operatorname{q}(i)>\alpha\})}{2 \beta}\end{gathered})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be a nonnegative integer and let i range from zero through n. Choose nonnegative integer powers q(i), with q(i) at most q(n), and real functions lambda(i,T). Fix positive constants beta, c, and C. Assume that for every sufficiently small positive T and every i, c T raised to q(i) is at most lambda(i,T), and lambda(i,T) is at most C T raised to q(i). No continuity is required of these functions. In the display, powerBounds denotes these simultaneous eventual inequalities together with c and C positive and q(i) at most q(n).

For every real alpha define I(alpha,T) as one half the sum over i of log(1+lambda(i,T)/(beta T raised to alpha)). Define R(alpha,T) as one half the sum of T raised to alpha divided by beta T raised to alpha plus lambda(i,T). For any positive variance schedule epsilon on all positive times, define R(epsilon,T) by replacing T raised to alpha in this latter expression with epsilon(T). All logarithms are natural.

For every real alpha, including values equal to one or more occupied powers, the difference between I(alpha,T) and one half the sum of max(alpha-q(i),0) times log(1/T) is bounded as T decreases to zero. R(epsilon,T) tends to zero exactly when epsilon(T) is little-o of T raised to q(n), for every positive schedule without a continuity or power-law assumption. If alpha differs from every q(i), R(alpha,T) tends to the number of indices with q(i) greater than alpha, divided by 2 beta. Repeated powers are counted with their full multiplicity.

Multiplying each logarithm's argument by T raised to max(alpha-q(i),0) puts it in the fixed positive interval from min(1,c/beta) to 1+C/beta. This gives a uniform bound for each logarithmic remainder. With delta(T)=epsilon(T)/T raised to q(n), all risk summands lie between zero and delta(T)/c, while the final summand is at least delta(T)/(beta delta(T)+C). Set v(T)=delta(T)/(beta delta(T)+C). The inverse relation delta=C v/(1-beta v) proves necessity of the recovery condition. The strict-threshold limit follows by separating powers above and below alpha.

## Noise selection of observable derivative layers

Fix d,p>=1, real matrices B of size d by d and C of size p by d, and beta>0. Assume finite observability: C B^k x=0 for every 0<=k<d implies x=0. Put V_0=R^d, V_j=the intersection of ker(C B^k) for 0<=k<j, m=the least j with V_(j+1)=0, E_j=V_j intersect the orthogonal complement of V_(j+1), and d_j=dim E_j. Then m<d, d_m>0 and R^d is the orthogonal sum of E_0 through E_m. Fix B,C, the Euclidean norms and the time unit throughout the limit T down to zero through positive values.

For every T>0, the trajectory map F_T sends x to the L2 class of t mapped to C exp(t B)x on (0,T]. The construction and injectivity in `D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates` give a d-dimensional image and hence an orthonormal image basis. Any bounded linear trajectory representative with this almost-everywhere formula equals F_T by equality of L2 classes. For any orthonormal basis b_(T,i) of that image, form the coordinate map U_T by projecting onto the image and applying its basis isometry. Its coordinates are the integrals of inner(b_(T,i)(t),g(t)) from zero to T. M_T is the matrix of U_T F_T. Since U_T is isometric on the image, M_T transpose M_T=F_T adjoint F_T=G(T), where G(T) is the integral of exp(t B transpose) C transpose C exp(t B) from zero to T. Thus all representatives and all orthonormal image bases give the same Gramian; neither a Gramian factor nor a spectral bound is an extra assumption.

On any probability space let X and xi be independent measurable random vectors with laws N(0,beta inverse I_d) and N(0,I_d). For any real amplitude sigma(T) with v(T)=sigma(T)^2>0 set Y_T=M_T X+sigma(T) xi. These are d finite normalized integral readings with independent isotropic coordinate noise. The law mu_T of (Y_T,X) is the actual pushforward of the same independent Gaussian pair, and I_T is the ENNReal KL divergence of mu_T from the product of its two marginals. Define R_T as the ENNReal infimum, over every measurable map a:R^d to R^d, of the nonnegative integral of ||X-a(Y_T)||^2/2. Infinite-risk competitors remain in this infimum. There is no white-noise random function in L2 in this experiment.

The posterior disintegration in `D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law` applies with M=M_T and tau=v(T) inverse. Its covariance is Sigma_T=(beta I+v(T) inverse G(T)) inverse and its mean is v(T) inverse Sigma_T M_T transpose Y_T. The KL value is finite and equals one half log det(I+G(T)/(beta v(T))). Under each posterior, the conditional squared-loss integral for a is trace(Sigma_T)/2+||posterior mean-a(Y_T)||^2/2. Tonelli for the joint disintegration proves this identity for every measurable a, even when its risk is infinite. The linear posterior mean attains the infimum, so R_T=ofReal(trace(Sigma_T)/2) and R_T is finite. Real conversions of I_T and R_T below therefore preserve their values.

For the same posterior and prior, the expected conditional free-energy difference is beta inverse times I_T, with F(p)=expected ||x||^2/2 minus beta inverse times differential entropy. If B transpose=-B, exp(tB) is an isometry with inverse exp(-tB); composition with this inverse bijects all measurable future estimators. The future Bayes energy risk at every t>=0 is the same R_T. These are the information and risk quantities of the same Gaussian experiment.

The normalized physical scaling in `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian` acts on E_j by sqrt(T) T^j and has a positive polynomial Gramian limit. An orthonormal basis subordinate to the E_j, reordered by increasing layer label w_i, satisfies #{i:w_i=j}=d_j and max_i w_i=m. Orthogonal conjugacy preserves the ordered spectrum of the actual G(T). Applying `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum` in these coordinates gives constants c,K,delta>0 with c T^(2w_i+1)<=lambda_i(T)<=K T^(2w_i+1) for every i and 0<T<delta. All these objects come from the fixed observable B,C and the derivative filtration.

Diagonalizing this same G(T) expresses information as one half the sum of log(1+lambda_i(T)/(beta v(T))), and risk as one half the sum of v(T)/(beta v(T)+lambda_i(T)). Apply the finite-spectrum theorem above with n=d-1 and q(i)=2w_i+1. Grouping equal w_i counts exactly d_j terms. For every real alpha, with v(T)=T^alpha at every positive T, the information remainder is O(1), including alpha equal to occupied thresholds. The risk limit requires alpha unequal to 2j+1 only when d_j>0. Empty layers impose no exclusion.

$\begin{gathered}\operatorname{I}(\alpha, T)=\frac{1}{2}\sum_{j=0}^{m} d_{j} \operatorname{max}(\alpha-(2j+1), 0) \log(\frac{1}{T})+\operatorname{O}(1)\\{}\lim_{T\to0^{+}}\operatorname{R}(\alpha, T)=\frac{\sum_{j=0}^{m} d_{j} \operatorname{indicator}(2j+1>\alpha)}{2\beta}\\{}\operatorname{R}(v, T)\to0 \iff \operatorname{v}(T)=\operatorname{o}(T^{2m+1})\\{}\operatorname{I}(eta, T)=\frac{T}{2\beta eta}\operatorname{tr}(C^{T}C)+\operatorname{O}(T^{2})\end{gathered}$

In the display I_alpha and R_alpha use variance T^alpha, R_v uses an arbitrary schedule v:R to R positive at every T>0, and I_eta uses the constant variance eta>0. Each sum runs over j=0,...,m. In the risk-limit sum retain exactly the indices with 2j+1>alpha. The information coefficient is exactly one half, the unrecovered energy per direction is exactly 1/(2 beta), and the fixed-noise coefficient is exactly trace(C transpose C)/(2 beta eta). No monotonicity, continuity or measurability in T is imposed on v or on the family of trajectory bases. Every positive v admits an amplitude sigma(T)=sqrt(v(T)); either sign of any amplitude with that square gives the same laws.

For necessity and sufficiency of complete recovery set delta(T)=v(T)/T^(2m+1). The risk is at most d delta(T)/(2c), while one occupied last-layer direction contributes at least delta(T)/(2(beta delta(T)+K)). Thus risk tends to zero exactly when delta(T) tends to zero, which is precisely v=o(T^(2m+1)). This uses only the simultaneous two-sided spectral bounds and positivity of v. At an occupied equality alpha=2j+1 the information remains bounded in that layer; no universal risk limit is asserted there.

For constant eta, `D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information` gives constants A>=0 and epsilon>0 with |I_eta(T)-T trace(C transpose C)/(2 beta eta)|<=A T^2 for every 0<T<=epsilon. Its operator integral is this same G(T); standard orthonormal coordinates preserve determinant and trace. The fixed-noise clause uses the exponential observation directly and needs no observability assumption. Its first-order term reads the initial gain alone; it does not certify recovery of higher derivative layers. No conclusion about other unresolved operator-window alternatives is implied.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian`
- Truth anchor: `D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law`
- Truth anchor: `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum`
- Truth anchor: `D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates`
- Truth anchor: `D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information`
- Truth anchor: `D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics`
