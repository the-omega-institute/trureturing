# Countable Gaussian Quadratic Fourth Moment

## Abstract

Square-summable centered Gaussian quadratic series converge in L4 with exact second and fourth moments.

**Theorem 1.1 (Scalar central even moments).**

$$\forall mu \in \mathbb{R},\; \forall sigma \in NNReal,\; \forall n \in \mathbb{N},\; \operatorname{centralMoment}\left(id, 2 \cdot n, \operatorname{gaussianReal}\left(mu, sigma^{2}\right)\right) = sigma^{2 \cdot n} \cdot \operatorname{doubleFactorial}\left({2 \cdot n-1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.centralMoment_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

For every real mean mu, nonnegative standard deviation sigma and natural n, the Gaussian central moment of order 2n is sigma^(2n)(2n-1)!!. This includes n=0 and sigma=0. The countable quadratic-series moments and the same-noise centered-square construction use this scalar formula.

The scalar proof is ported from RemyDegenne/brownian-motion, BrownianMotion/Gaussian/Moment.lean, centralMoment_two_mul_gaussianReal, commit 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9, under Apache 2.0.

**Theorem 1.2 (Actual infinite sums and their moments).**

$$\forall Omega \in Type, Sigma \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega, Sigma\right), G \in {\mathbb{N}\to {Omega\to \mathbb{R}}}, a \in {\mathbb{N}\to \mathbb{R}},\; \left(\left(\left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\forall j \in \mathbb{N},\; \operatorname{HasLaw}\left(G(j), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right)\right) \land \operatorname{iIndepFun}\left(G, P\right)\right) \land \operatorname{Summable}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)\right) \Rightarrow \left(\exists hm \in \left(\forall j \in \mathbb{N},\; \operatorname{MemLp}\left((omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1)), 4, P\right)\right), X \in \operatorname{Lp}\left(\mathbb{R}, 4, P\right),\; \left(\left(\left(\left(\left(\operatorname{HasSum}\left((j:\mathbb{N}\mapsto \operatorname{toLp}\left(hm(j), (omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1))\right)), X\right) \land \operatorname{MemLp}\left(X, 2, P\right)\right) \land \operatorname{Tendsto}\left((s:\operatorname{Finset}\left(\mathbb{N}\right)\mapsto \operatorname{eLpNorm}\left({(omega:Omega\mapsto \operatorname{finsetSum}\left(s, (j:\mathbb{N}\mapsto (omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1))(omega))\right))-X}, 2, P\right)), atTop, \operatorname{nhds}\left(0\right)\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{1})\right) = 0\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{2})\right) = 2 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{4})\right) = 12 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)^{2}+48 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{4})\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{4})\right) \le 15 \cdot \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{2})\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let (Omega, Sigma, P) be any probability space. The countable family G(j) consists of independent real random variables with standard Gaussian law. Let a(j) be real coefficients whose squares are summable. Coefficients may be zero or negative, and their support may be infinite.

Write F(j)(omega)=a(j)(G(j)(omega)^2-1), T(s)(omega)=sum over j in the finite set s of F(j)(omega), and S=sum over j of a(j)^2. The theorem supplies proofs hm(j) that each actual term belongs to L4(P), and an element X of L4(P) to which their finite-subset sums converge in norm. The notation toLp(hm(j),F(j)) denotes the equivalence class of the actual function, modulo almost-everywhere equality. All integrals below use the measurable representative of X.

The representative X also belongs to L2(P), and eLpNorm(T(s)-X,2,P) tends to zero as s increases through all finite subsets. Its mean is zero, its second moment is 2S, and its fourth moment is 12S^2+48 sum over j of a(j)^4. In particular its fourth moment is at most fifteen times the square of its second moment. No higher integrability or series convergence is assumed.

For each finite subset, independence and the standard Gaussian even moments give the two exact moment identities. The fourth-power coefficient sum is at most the square of the square-sum, so every finite tail has fourth moment at most sixty times its coefficient square-sum squared. Completeness of L4 constructs the sum. Norm continuity passes the fourth moment to the limit, and exponent comparison gives the L2 and mean conclusions.

This is a coefficient-series moment calculation using classical Gaussian facts. The cited fixed-chaos literature provides related fourth-moment context; no claim of mathematical novelty is made. Identifying a prescribed spectral series with X requires equality of its L2 limit. This result alone asserts neither process tightness nor a stable limit.

Weighted Gaussian spectral applications.

For an arbitrary universe and index type I, take real functions t,w on I and real parameters a,m. Assume a>0, 3<=2*m*a^2, w(i)>=0 and a<=|t(i)| for every i, and Summable(i -> w(i)/t(i)^2). Then the full weighted shell is summable and satisfies sum_i w(i)(|t(i)|+1)exp(-m*t(i)^2) <= a^2(a+1)exp(-m*a^2) sum_i w(i)/t(i)^2. The sum is the unconditional tsum on I; countability, distinct ordinates, local finiteness, enumeration order and a finite-subset replacement are not assumptions. The threshold itself implies m>0.

The exact reduction uses x=|t(i)|, r=x/a>=1 and b=m*a^2>=3/2. With x=a*r, the polynomial difference a^2(a+1)r^3-x^2(x+1)=a^2*r^2*(r-1) is nonnegative. Real.add_one_le_exp(r-1) and Real.exp_nat_mul give r^3<=exp(3(r-1)). The identity b(r^2-1)-3(r-1)=(b-3/2)(r^2-1)+(3/2)(r-1)^2 gives the required exponential comparison. Multiplying yields x^2(x+1)exp(-m*x^2)<=a^2(a+1)exp(-m*a^2). Since t(i)^2>0, multiply by the nonnegative w(i)/t(i)^2. Summable.of_nonneg_of_le against the summable scalar multiple of the mass proves summability before tsum_le_tsum and tsum_mul_left establish the displayed bound.

The same formula includes an empty index, an arbitrary uncountable index with zero weights, either sign at x=a with 2*m*a^2=3, and infinitely repeated ordinates of absolute value 2 with geometric weights (1/2)^n. Zero weights are permitted. Both signs and repetitions are carried by I and are never quotiented away. These follow from the exponential and nonnegative-series comparison results.

For the full complex Gaussian calculation set c=16*m, q=(y-c)/(2*m), d_m(y)=exp(-(y-c)^2/(4*m))/sqrt(4*pi*m), A(y)=3(y+1)(q^2+gamma^2+1)d_m(y), and M(z)=exp(m*z^2+16*m*z). Here m>0, gamma is any real and z is any complex number. Mathlib complexMGF_id_gaussianReal at mean 16*m and variance 2*m, integrableExpSet_id_gaussianReal, iteratedDeriv_complexMGF and integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet give the full complex moments and integrability. gaussianReal_of_var_ne_zero, integral_gaussianReal_eq_integral_smul and integrable_withDensity_iff_integrable_smul transport them to this Lebesgue density. These applications retain the positive variance and all complex tilts.

Writing u=16*m+2*m*z, the degree-zero through degree-three moments are M(z), u*M(z), (u^2+2*m)*M(z), and (u^3+6*m*u)*M(z). Expand (y+1)(q^2+gamma^2+1) with coefficients a3=1/(4*m^2), a2=(1-2*c)/(4*m^2), a1=(c^2-2*c)/(4*m^2)+gamma^2+1, and a0=c^2/(4*m^2)+gamma^2+1. Finite integral linearity on the four integrable monomials gives P(z)M(z), where P(z)=(16*m+2*m*z+1)(z^2+gamma^2+1+1/(2*m))+2*z. The covariance term +2*z remains. Multiplication by 3 evaluates the integral with A. Norm integrability also holds at the real tilts 1 and -2.

For the weighted spectral application let Z have the original seven fields: a natural-occurrence zero function, 0<Re(zero)<1, 10<|Im(zero)|, summability of inverse ordinate squares, their full sum R<2, finiteness of every inclusive height cutoff T>=10, and its two-sided count <=floor(2*T^2). No injectivity or critical-line condition is required. Put r(rho,h)=1/(rho*(1+h-rho)), K(h,y)=sum_n exp((Z.zero(n)-h)*y)r(Z.zero(n),h), and h in the entire interval [0,2]. Both denominators are nonzero and |r|<=1/Im(rho)^2. The norm exponential is bounded by exp(y) for y>=0 and exp(-2*y) for y<=0. Nonnegative comparison first proves all-index norm summability, then bounds its sum by (exp(y)+exp(-2*y))*R.

The actual product majorant is B(y,h)=|A(y)|(exp(y)+exp(-2*y))*(1+|h|)*R on Lebesgue measure times the restricted [0,2] measure. Gaussian monomial integrability supplies the y factor, compact-interval continuity supplies the h factor, and Integrable.mul_prod supplies their product. Integrable.mono_nonneg and Integrable.mono' give integrability of the norm series, every term and the full complex sum. Finite sums of integrals of term norms are bounded by the integral of B; summable_of_sum_le therefore supplies the premise of integral_tsum_of_summable_integral_norm. This pays the Bochner exchange before integral_prod and integral_prod_symm. The y-integral is the full complex 3*P(Z.zero(n)-h)*M(Z.zero(n)-h), with no reality or parity replacement.

Let Full=sum_n integral_[0,2] 3(1+h)r(Z.zero(n),h)P(Z.zero(n)-h)M(Z.zero(n)-h), Low=integral_(1,infinity) A(y) integral_[0,2](1+h)K(h,y), Eplus=-integral_(0,1] of the same integrand, and Eminus=-integral_(-infinity,0) of it. integral_add_compl, setIntegral_union and the null singleton give Low=Full+Eplus+Eminus. Every real gamma and every m>0 are allowed for this identity and the original integrability assertions.

For m>=1 and gamma>10 write D=gamma+10 and t=|Im(rho)|>10. Strip, the entire h-window and complex norm inequalities give |rho-h|<=2*t, |16*m+2*m*(rho-h)+1|<=6*m*t, and |(rho-h)^2+gamma^2+1+1/(2*m)|<=4*t^2+D^2. Divide the numerator bound 24*m*t^3+6*m*D^2*t+4*t by the actual denominator lower bound t^2. With D^2>=24 this yields |r*P|<=2*m*D^2*(t+1), hence also the original core 20 bound. For x=Re(rho)-h in [-2,1], (1-x)(17+x)>=0 gives x^2+16*x<=17, so the remaining exponential norm is <=exp(17*m)exp(-m*t^2).

The exact h weight has integral_[0,2](1+h)=4; including the physical 3 gives 12. norm_integral_le_integral_norm gives integrated coefficient 24 from core 2 and 240 from core 20. The shell is summable by the reciprocal-mass formula with I=N, t(n)=Im(Z.zero(n)), w(n)=1, a=10 and unchanged m>=1, since 3<=200*m. It satisfies shell<=1100*R*exp(-100*m)<=2200*exp(-100*m)<=10000*exp(-100*m). Thus the original all-index complex series is absolutely summable and |Full|<=240*m*D^2*shell*exp(17*m)<=m*D^2*2400000*exp(-83*m). This preserves the original constant and exponent. The separate finite-shell induction proves the same old 10000 bound on the original seven fields; it is unnecessary for this reuse derivation.

For the extensions, the same summable-series comparison gives |integral_[0,2](1+h)K|<=4*c*R<=8*c whenever each exponential norm is <=c. On 0<y<=1 take c=3. There d_m<=1, q in [-8,0] and |A|<=6*D^2, yielding |Eplus|<=144*D^2<=2400*m*D^2. For y<0, completing the square gives d_m(y)exp(-2*y)=exp(-28*m)*pdf_(12*m,2*m)(y). With v=y-12*m, the nonnegative polynomial majorant is H(v)=(13*m+1+v^2/(4*m))*(v^2/(2*m^2)+gamma^2+9). The first factor uses |v|<=m+v^2/(4*m); the second bounds (v/(2*m)-2)^2.

The actual negative majorant is integrable by Gaussian power integrability and density transport. The existing centralMoment_two_mul theorem in this result owner, at orders 2 and 4 and sigma=sqrt(2*m), gives E[v^2]=2*m and E[v^4]=12*m^2, with its original RemyDegenne/brownian-motion attribution unchanged. The exact expectation of H is (13*m+3/2)(gamma^2+9)+13+5/(2*m)<=16*m*D^2 under m>=1 and gamma>10. Restriction to y<0 and setIntegral_le_integral then give |Eminus|<=24*exp(-28*m)*16*m*D^2=384*m*D^2*exp(-28*m). This supplies the actual integrable majorant and both moments.

Triangle inequality now gives the original conclusion: the defining low-height integrand is integrable on (1,infinity) and |Low|<=m*(gamma+10)^2*(2400000*exp(-83*m)+2400+384*exp(-28*m)) for m>=1 and gamma>10. The derivation uses the scalar central moments and the explicit upstream Gaussian, series and integration results. Its shell estimate alone does not prove a sharper complete weighted endpoint, a Robin sign, retained Schur domination, a completed carrier or RH. The complete-zero realization and the height-derived first Li mass substitution are described in the actual mass owner exposition.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.centralMoment_two_mul`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.result`
