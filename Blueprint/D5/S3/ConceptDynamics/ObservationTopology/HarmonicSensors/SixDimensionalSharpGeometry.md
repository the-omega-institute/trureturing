# Physical correlation on a rescaled moving domain

## Abstract

Sharp physical chord gains and rank-defect limits for the six-coordinate paired sensor.

**Theorem 1.1 (The sharp normalized correlation maximum).**

$$\operatorname{Tendsto}\left((\varepsilon: \mathbb{R}) \mapsto \frac{\operatorname{actualEta}\left(\varepsilon\right)}{\sqrt{\varepsilon}}, \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{1}{2 \cdot \sqrt{2}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_eta_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For epsilon>0, let Z=9+20epsilon and take the paired frequencies 2, 3 and 4 with amplitudes sqrt(epsilon)/sqrt(Z), 1/sqrt(Z), and sqrt(epsilon)/sqrt(Z). The sensor has the real cosine and sine coordinate pair for each frequency. Its two-delay matrix has rows given by the sensor at phi and at phi-pi/6. For two distinct physical circle states, form the difference of these matrices. The quantity actualRank(epsilon) is the infimum of its Frobenius-norm square divided by its Euclidean operator-norm square over every such pair of states. Define actualEta(epsilon)=2/actualRank(epsilon)-1.

In the statement, Tendsto is convergence of a real-valued function between filters, nhds is the neighborhood filter on the real line, and nhdsWithin(0,Ioi(0)) is the neighborhood filter of zero within (0,infinity). Thus the limit is taken as epsilon tends to zero through strictly positive real values, and its value is exactly 1/(2sqrt(2)).

For 0<epsilon<=1/2, the row Gram matrix has diagonal entries E and off-diagonal entries C, where E is the common row energy and C is the row correlation. Its eigenvalues are E+C and E-C. Hence the Frobenius-norm square is 2E and the operator-norm square is E+|C|. With q=4cos((phi-psi)/2)^2-1, the absolute correlation ratio is Q(epsilon,q)=(epsilon/2)|q(q+1)(2-q)|/[q^2(1+epsilon(q-1))+2epsilon]. On this same range 0<epsilon<=1/2, actualEta(epsilon) is the maximum of Q(epsilon,q) over -1<=q<=3, and actualRank(epsilon)=2/(1+max Q). Every -1<=q<3 is realized by a pair of distinct physical circle states; q=3 is approached by short chords.

Put t=sqrt(epsilon) and q=tz. The normalized quotient Q(epsilon,tz)/t equals S(t,z)=|z(1+tz)(2-tz)|/[2(z^2(1+t^2(tz-1))+2)]. The limiting profile is L(z)=|z|/(z^2+2). If t>=0, R>=0, |z|<=R, tR<=1 and t^2<=1/4, then |S(t,z)-L(z)| is at most (tR^2+t^2R^3)/4+R^3t^2(1+tR)/4. For fixed R this bound tends to zero as t tends to zero, giving uniform convergence on bounded intervals.

The rescaled physical domain is -1/t<=z<=3/t. If 0<epsilon<=1/4, R>0 and |z|>=R within this domain, the normalized quotient is at most 4/R. Taking R=32 makes this tail bound 1/8, strictly below the maximum 1/(2sqrt(2)) of L. The point z=sqrt(2) attains that limiting maximum and belongs to the rescaled domain for all sufficiently small positive epsilon. The bounded-interval estimate and tail bound give the upper limit bound, while this realized point gives the lower limit bound.

The definitions chordGain, gainValues, lowerGain and upperGain use the actual sensor chord divided by the Euclidean chord of circleState, with all pairs of distinct physical states included. The identity chord_gain_sq gives chordGain^2=P(epsilon,q)/Z, where P(epsilon,q)=q^2(1+epsilon(q-1))+2epsilon. For 0<epsilon<=1/2 and -1<=q<=3, the coefficient 1+epsilon(q-1) is nonnegative, so P>=2epsilon. The value q=0 is realized by a third-turn chord and attains equality. Taking the infimum therefore gives lowerGain^2=2epsilon/(9+20epsilon).

On the same parameter range, q^2<=9 and 1+epsilon(q-1)<=1+2epsilon give P<=9+20epsilon. Thus every physical chord gain is at most one. Differentiating each cosine-sine pair gives squared speed sum_i a_i^2 k_i^2=(4epsilon+9+16epsilon)/Z=1 at every phase. This derivative normalization requires only epsilon>0, so it holds on the entire positive parameter range. The global upper chord bound here uses epsilon<=1/2. The physical circle also has unit speed. The quotient of their short-chord lengths tends to one as d tends to zero from above. More explicitly, coordinate differentiation followed by the linear toLp map gives the derivative in the six-dimensional Euclidean space; sin^2+cos^2=1 reduces its norm square to the displayed budget at every phi. The one-sided slope-limit law at phase zero applies separately to sensor and circleState, and the denominator limit is one, so chordGain(epsilon,d,0) tends to one. These short physical states are eventually distinct. The gainValues set is nonempty and bounded above by one, while each short-chord gain lies below its supremum. Passing to the limit gives one<=upperGain; the uniform bound gives upperGain<=1. Thus for every 0<epsilon<=1/2, every phase has unit derivative norm and the actual sSup of all physical chord gains equals one.

**Theorem 1.2 (Rank defect relative to the least physical chord gain).**

$$\operatorname{Tendsto}\left((\varepsilon: \mathbb{R}) \mapsto \frac{2 - \operatorname{actualRank}\left(\varepsilon\right)}{\operatorname{lowerGain}\left(\varepsilon\right)}, \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{3}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_rank_defect_lower_gain_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here actualRank retains the infimum of the actual two-delay Frobenius norm squared divided by the actual Euclidean operator norm squared, at the fixed delay pi/6. The lowerGain in the denominator is the infimum of the sensor-to-circle chord norm ratio over all distinct physical state pairs. The limit is through strictly positive epsilon.

The correlation maximum characterization gives 2-actualRank=2actualEta/(1+actualEta) for 0<epsilon<=1/2. The established actual_eta_scaled_limit and sqrt(epsilon)->0 imply actualEta->0. Using sqrt(epsilon/2)=sqrt(epsilon)/sqrt(2), actual_rank_defect_scaled_limit gives (2-actualRank)/sqrt(epsilon/2)->1. The sharp lower gain formula gives lowerGain/sqrt(epsilon)=sqrt(2/(9+20epsilon)), which tends to sqrt(2)/3. Dividing these limits and the constant sqrt(2) yields the stated value 3/2.

The minimum of three frequency pairs and nonattainment of rank two for every finite injective harmonic family are separate assertions. Neither assertion follows from this fixed six-coordinate family and its small-epsilon asymptotics.

## The weighted observation experiment

This application uses the existing six-coordinate sensor and finite-product Gaussian laws. Fix epsilon>0, an arbitrary finite index set J (possibly empty), arbitrary real weights w_j and delays t_j, and sigma>0. Put phi_false=0 and phi_true=2pi/3. With K=Fin 3 x Fin 2 and B=EuclideanSpace R K, define s_b(j)=w_j sensor(epsilon,phi_b-t_j). Thus the three cosine-sine pairs retain frequencies 2, 3 and 4 and amplitudes sqrt(epsilon)/sqrt(9+20epsilon), 1/sqrt(9+20epsilon), sqrt(epsilon)/sqrt(9+20epsilon). The weights may be negative or zero; neither the delays nor the weights require normalization. The Gaussian argument imposes no upper bound on epsilon, so the restriction epsilon<=1/2 used for the sharp chord bounds above is not an assumption here.

Let Omega be a measurable space and let mu_b be a probability measure for each label b in Bool. For each j, let xi_bj:Omega -> B be mu_b-almost-everywhere measurable. Assume, separately for each b, that the family (xi_bj)_j is independent and that every component has law G_sigma=multivariateGaussian(0,sigma^2 I_K). These are real centered isotropic six-dimensional noises. Define the actual random observation Y_b(omega)(j)=s_b(j)+xi_bj(omega) and its law P_b=(mu_b).map(Y_b) on O=J -> B. Noise is added AFTER the signed weight multiplies the signal: its covariance is sigma^2 I_K even when w_j=0. In particular, this is not the model w_j(sensor+xi_bj). No independence, equality of samples or coupling between the two labels is assumed.

Write N_block=Measure.pi(j -> G_sigma). Independence and the component laws imply the actual joint identity (mu_b).map(omega -> (j -> xi_bj(omega)))=N_block by iIndepFun.map_fun_eq_pi_map. Consequently P_b=N_block.map(z -> s_b+z), using aemeasurable_pi_lambda and AEMeasurable.map_map_of_aemeasurable. Thus the product noise law is derived from the stated random variables; it is not an additional desired-law premise.

## The actual flattening and its inverse

Fix the coordinate bijection r:Fin 6 -> K characterized by r(2i+k)=(i,k), for i in Fin 3 and k in Fin 2. Set V=EuclideanSpace R (J x Fin 6). Define A:O -> V by (A y)(j,l)=y(j)(r(l)), with the Euclidean toLp constructor on the output, and Ainv:V -> O by (Ainv x)(j)(k)=x(j,r^{-1}(k)), again using toLp for each B-valued block. These are the actual coordinate maps, with Ainv composed with A equal to id_O and A composed with Ainv equal to id_V. Coordinatewise addition and scalar multiplication show linearity. Finite coordinate evaluation and the toLp maps show continuity in both directions; hence both maps are measurable and give a continuous linear equivalence O equivL[R] V.

The usual Pi norm on O is the maximum of the block Euclidean norms, whereas the norm on V is the square root of the sum of all squared coordinates. The displayed equivalence is not asserted to be an isometry for those norms. The finite reindexing r merely identifies the sensor owner's K=Fin 3 x Fin 2 with Fin 6: before that reindexing the same flattening has target EuclideanSpace R (J x K) and coordinates (j,k) -> y(j)(k). Thus it preserves the actual sensor coordinates and fixes exactly which six-coordinate convention is used.

Define m_b=A(s_b), explicitly m_b(j,l)=w_j sensor(epsilon,phi_b-t_j)(r(l)); set N=multivariateGaussian(0,sigma^2 I_(J x Fin 6)) and Q_b=multivariateGaussian(m_b,sigma^2 I_(J x Fin 6)). The identities to be obtained are N_block.map(A)=N, P_b.map(A)=Q_b, Q_b=N.map(x -> m_b+x), and Q_b.map(Ainv)=P_b. The covariance sigma^2 I is on all 6|J| flattened coordinates, independently of the signed weights.

## Deriving the Gaussian law from scalar products

For any finite coordinate type L, let R_L=Measure.pi(l -> gaussianReal(0,1)), the product of scalar standard Gaussian probability measures. The affine definition of ProbabilityTheory.multivariateGaussian is the pushforward of stdGaussian by x -> m+toEuclideanCLM(CFC.sqrt(S))x. Since sigma>=0, Matrix.PosSemidef.one.smul makes sigma I positive semidefinite, and CFC.sqrt_mul_self applied to (sigma I)(sigma I)=sigma^2 I gives CFC.sqrt(sigma^2 I)=sigma I. ProbabilityTheory.map_pi_eq_stdGaussian then yields multivariateGaussian(m,sigma^2 I_L)=R_L.map(u -> m+sigma toLp(u)). This uses the positive matrix square root and the affine definition, with no added orthogonality assumption.

Apply this identity first with L=K and m=0. Measure.pi_map_pi says that N_block is the pushforward of T=Measure.pi(j -> R_K) by u -> (j -> sigma toLp(u(j))). The coordinate rearrangement U(u)(j,l)=u(j)(r(l)) sends T to R_(J x Fin 6). To see the actual law equality, take arbitrary measurable coordinate sets a_(j,l). The preimage of their product rectangle is the nested rectangle whose j-th factor has k-th set a_(j,r^{-1}(k)). Measure.pi_pi computes its mass as product_j product_k gaussianReal(0,1)(a_(j,r^{-1}(k))). Reindex the inner finite product by r and use Finset.prod_product to obtain product_(j,l) gaussianReal(0,1)(a_(j,l)). Measure.pi_eq identifies the measures from these rectangle values. This argument also covers the empty product.

The coordinate identity A(j -> sigma toLp(u(j)))=sigma toLp(U(u)) and Measure.map_map now give N_block.map(A)=R_(J x Fin 6).map(v -> sigma toLp(v))=N. With the same scalar-product formula at m=m_b, translation gives N.map(x -> m_b+x)=Q_b. Linearity gives A(s_b+z)=m_b+A(z), so the already derived P_b=N_block.map(z -> s_b+z) implies P_b.map(A)=Q_b. Finally Measure.map_map and Ainv composed with A=id_O give Q_b.map(Ainv)=P_b. In particular, both directions concern the original observation law, rather than a substituted Gaussian experiment.

## Every measurable classifier and the empty experiment

For every measurable classifier delta:O -> Bool, the transported classifier delta composed with Ainv is measurable. For each true label b and each event label c in Bool, Measure.map_apply applied to Q_b.map(Ainv)=P_b gives P_b({y | delta(y)=c})=Q_b({x | delta(Ainv(x))=c}) as an equality in ENNReal. Applying ENNReal.toReal gives the real-probability equality (P_b).real({y | delta(y)=c})=(Q_b).real({x | delta(Ainv(x))=c}). All these measures are probabilities, so these event values are finite.

Conversely, for every measurable h:V -> Bool, h composed with A is measurable and, for every b,c in Bool, P_b({y | h(A(y))=c})=Q_b({x | h(x)=c}) in ENNReal, with (P_b).real({y | h(A(y))=c})=(Q_b).real({x | h(x)=c}) after ENNReal.toReal. This follows from P_b.map(A)=Q_b and Measure.map_apply. Both assertions quantify over all measurable classifiers and both Boolean events; they are not restricted to threshold rules.

If J is empty, O and V each have only their zero vector and s_b=m_b=0. Measure.pi_of_empty gives N_block=Measure.dirac(0); its translated pushforward gives the actual P_b=Measure.dirac(0), and flattening gives the actual Q_b=Measure.dirac(0). Thus the inverse maps, Gaussian law identifications and both classifier probability equalities include the zero-dimensional experiment without a nonempty-index hypothesis.

The parameter binding is sigma to the positive noise scale, s to the actual weighted harmonic means s_b, mu to the two original per-label probability measures, and xi to their independent B-valued noise coordinates. The sensor definition belongs to SixDimensionalSharpGeometry; the affine Gaussian, independence, finite-product and pushforward suppliers are existing public Mathlib results at pin db584cd6d46c92f209a44c0f1c829460d327499d, recorded in lake-manifest.json. This is an application of those results, with the coordinate reindexing written explicitly, not an additional Lean theorem or a new library result. GaussianObservationLaw separately owns its posterior, likelihood and information statement; that statement is not needed as a premise here.

This application establishes the block-noise experiment, its actual Gaussian flattening and exact all-classifier event-probability transport. It does not establish a scalar score/residual decomposition, a reconstruction kernel, an optimized global risk formula, an energy or quantile bound, a design cap or an asymptotic risk law. Those would require their own assumptions and arguments beyond the law and probability identities given here.

## The actual score and orthogonal residual

Continue the same weighted observation experiment with 0<epsilon<=1/2, sigma>0, arbitrary finite J, signed real weights w_j and real delays t_j. The preceding block-noise and flattening argument supplies C01/C02; the following score and reconstruction argument supplies C03/C04. Use its actual flattened means m_b=A(s_b), covariance S=sigma^2 I, centered law N=multivariateGaussian(0,S), and observation laws Q_b=multivariateGaussian(m_b,S)=N.map(x -> m_b+x). All formulas use the same Fin 6 reindexing of K=Fin 3 x Fin 2 already specified; equivalently they can be written in EuclideanSpace R (J x K) before reindexing. The weights still multiply only the sensor signal, and the isotropic noise is added afterwards. No target score law, residual law, independence or support statement is an extra hypothesis.

Set d=m_true-m_false, D=norm(d), and c=(m_false+m_true)/2. For D>0 define u=D^{-1} d, alpha(x)=inner(u,x), and P_perp(x)=x-alpha(x)u. Thus alpha=innerSL R u and P_perp=id-alpha.smulRight(u) are continuous linear maps. Put beta_false=-D/2, beta_true=D/2, lambda_b=gaussianReal(beta_b,sigma^2), and nu=N.map(P_perp); sigma^2 is viewed as a nonnegative real parameter in gaussianReal. Define the actual score T(y)=alpha(y-c), residual R(y)=P_perp(y-c), F(y)=(T(y),R(y)), and G(r,z)=c+r u+z. These maps are measurable. The product target uses this particular pushforward nu of the actual centered noise.

Normalization gives norm(u)=1, alpha(u)=1 and D u=d, whence m_b-c=beta_b u. Directly from the formula for P_perp, alpha(P_perp x)=0, P_perp(u)=0, P_perp(P_perp x)=P_perp x, and inner(v,P_perp x)=inner(P_perp v,x). Its range equals ker(alpha): the first identity gives one inclusion, and alpha(z)=0 implies P_perp(z)=z for the other. These identities use D>0 only to obtain the unit direction; no unit vector is asserted when D=0.

## Joint Gaussianity, independence and the product law

On the single probability space (V,N), start with the actual pair x -> (alpha(x),P_perp(x)). IsGaussian.hasGaussianLaw_id and HasGaussianLaw.map_fun applied to the continuous linear map alpha.prod(P_perp) give its joint Gaussian law. Matrix.PosSemidef.one.smul makes S positive semidefinite, and covarianceBilin_multivariateGaussian gives covarianceBilin(N)(v,w)=sigma^2 inner(v,w). For every real a and vector v, self-adjointness of P_perp therefore gives Cov_N(inner(a,alpha(x)),inner(v,P_perp(x)))=sigma^2 inner(a u,P_perp(v))=sigma^2 a alpha(P_perp(v))=0. This checks all scalar cross-covariances. HasGaussianLaw.indepFun_of_covariance_inner now derives independence of alpha and P_perp from their common joint Gaussian law; separate Gaussian marginals alone would not supply that inference.

The centered score has integral zero: commute alpha with integration and use integral_id_multivariateGaussian. Its variance is covarianceBilin(N)(u,u)=sigma^2 because norm(u)=1. For each b, translation by m_b sends N to Q_b and F(m_b+x)=(beta_b+alpha(x),P_perp(x)). Hence under Q_b the actual T is Gaussian with expectation beta_b and variance sigma^2. HasGaussianLaw.map_eq_gaussianReal identifies Q_b.map(T)=lambda_b. Independence survives adding beta_b to the first component by IndepFun.comp; IndepFun.map_prod_eq_prod_map_map then gives Q_b.map(F)=lambda_b.prod(nu). The second component of the same translation identity gives Q_b.map(R)=nu for both labels. Thus the label information appears only in the score mean; the common residual and product law are derived from the original Q_b.

The identity alpha(P_perp x)=0 also proves nu(ker(alpha))=1 by Measure.map_apply, since the preimage of that closed kernel is all of V and N has mass one. The residual is allowed to be singular on the ambient space: no invertible residual covariance or ambient Lebesgue density is assumed. Both labels use exactly N.map(P_perp), with its full mass on the same orthogonal hyperplane.

## Reconstruction and one label-independent Markov kernel

For every y in V, cancellation in c+alpha(y-c)u+((y-c)-alpha(y-c)u) gives the GLOBAL identity G(F(y))=y. In the other direction, for every real r and every z with alpha(z)=0, alpha(r u+z)=r and P_perp(r u+z)=z, so F(G(r,z))=(r,z). This second identity is asserted on R x ker(alpha), a set of full lambda_b.prod(nu) measure, rather than on all of R x V. Applying Measure.map_map to Q_b.map(F)=lambda_b.prod(nu) and the global G-after-F identity gives the exact reverse law (lambda_b.prod(nu)).map(G)=Q_b for each b.

Define kappa(r)=nu.map(z -> c+r u+z), using the SAME c, u and nu for both labels. A concrete measurable kernel is ((Kernel.id : Kernel R R) x_kernel Kernel.const R nu).map(G); Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply and Measure.dirac_prod give the displayed value at every r. Since nu is a probability measure and G is measurable, Kernel.IsMarkovKernel.map makes kappa a Markov kernel. There is no label argument in its definition, and no desired conditional law is assumed.

To obtain the actual score-observation joint law, set H(r,z)=(r,G(r,z)). For every measurable E in R x V, Measure.compProd_apply integrates kappa(r)({y | (r,y) in E}) against lambda_b. Substitute the explicit kappa and use Measure.map_apply and Measure.prod_apply: this integral is (lambda_b.prod(nu))(H^{-1}(E)). Consequently lambda_b compProd kappa=(lambda_b.prod(nu)).map(H). Substituting Q_b.map(F) for the product and using H(F(y))=(T(y),y), by the global inverse, proves Q_b.map(y -> (T(y),y))=lambda_b compProd kappa. This identifies the true joint law, beyond a reconstruction marginal. Taking its second marginal yields (lambda_b compProd kappa).map(Prod.snd)=Q_b. Finally F(G(r,z))=(r,z) on the full-nu kernel gives (kappa(r)).map(T)=Measure.dirac(r) for EVERY real r, including values outside any chosen almost-everywhere version.

## Coincident means, empty designs and remaining limits

If D=0, norm(d)=0 implies m_true=m_false, hence Q_true=Q_false. Use the constant score T_0(y)=0 and the constant Markov kernel kappa_0(r)=Q_false for every real r. Then Q_b.map(T_0)=Measure.dirac(0), and Measure.compProd_const together with Measure.dirac_prod gives Q_b.map(y -> (0,y))=Measure.dirac(0) compProd kappa_0. Its second marginal is Q_b. This branch uses neither division by D nor a unit direction, and its score variance is zero, not sigma^2. The nondegenerate identity (kappa(r)).map(T)=dirac(r) is not extended to every r for this constant-score kernel.

If J is empty, the flattened coordinate space has only its zero vector. Thus m_b=0, D=0, N=Measure.dirac(0) and Q_b=Measure.dirac(0); the original P_b is also the zero Dirac law by the preceding flattening argument. Every probability measure on that singleton is the zero Dirac law, so this is the actual empty experiment, not a limiting positive-dimensional model. Arbitrary zero weights and coincident means are likewise handled by the D=0 branch without assuming J nonempty.

The sensor and its weighted means remain those of SixDimensionalSharpGeometry. The Gaussian mapping, covariance, independence, pushforward and kernel arguments apply the existing public Mathlib suppliers named above, at pin db584cd6d46c92f209a44c0f1c829460d327499d. Together with C01/C02, these identities retain the original C03/C04 score, common residual, reverse law and shared Markov joint law as an application of existing results. C05-C13 remain open here: optimized global risk, energy or quantile bounds, design caps and asymptotic risk laws require their own assumptions and arguments. No conclusion about completion of the parent problem follows.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_eta_scaled_limit`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_rank_defect_lower_gain_limit`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts](../CircleGraphCharts.md)
