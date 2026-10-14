using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors;

internal sealed class SixDimensionalSharpGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp physical chord gains and rank-defect limits for the six-coordinate paired sensor.",
        H("Physical correlation on a rescaled moving domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sixdimensionalsharpgeometry-actual-eta-scaled-limit"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_eta_scaled_limit"),
                H("The sharp normalized correlation maximum"),
                StatementSource.FromAuthor(ActualEtaLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For epsilon>0, let Z=9+20epsilon and take the paired frequencies 2, 3 and 4 "
                        + "with amplitudes sqrt(epsilon)/sqrt(Z), 1/sqrt(Z), and sqrt(epsilon)/sqrt(Z). "
                        + "The sensor has the real cosine and sine coordinate pair for each frequency. "
                        + "Its two-delay matrix has rows given by the sensor at phi and at phi-pi/6. "
                        + "For two distinct physical circle states, form the difference of these matrices. "
                        + "The quantity actualRank(epsilon) is the infimum of its Frobenius-norm square "
                        + "divided by its Euclidean operator-norm square over every such pair of states. "
                        + "Define actualEta(epsilon)=2/actualRank(epsilon)-1.")),
                    Paragraph(Text(
                        "In the statement, Tendsto is convergence of a real-valued function between "
                        + "filters, nhds is the neighborhood filter on the real line, and "
                        + "nhdsWithin(0,Ioi(0)) is the neighborhood filter of zero within (0,infinity). "
                        + "Thus the limit is taken as epsilon tends to zero through strictly positive "
                        + "real values, and its value is exactly 1/(2sqrt(2)).")),
                    Paragraph(Text(
                        "For 0<epsilon<=1/2, the row Gram matrix has diagonal entries E and "
                        + "off-diagonal entries C, where E is the common row energy and C is the "
                        + "row correlation. Its eigenvalues are E+C and E-C. Hence the Frobenius-norm "
                        + "square is 2E and the operator-norm square is E+|C|. With "
                        + "q=4cos((phi-psi)/2)^2-1, the absolute correlation ratio is "
                        + "Q(epsilon,q)=(epsilon/2)|q(q+1)(2-q)|/[q^2(1+epsilon(q-1))+2epsilon]. "
                        + "On this same range 0<epsilon<=1/2, actualEta(epsilon) is the maximum "
                        + "of Q(epsilon,q) over -1<=q<=3, and actualRank(epsilon)=2/(1+max Q). "
                        + "Every -1<=q<3 is realized by a pair of distinct physical circle states; "
                        + "q=3 is approached by short chords.")),
                    Paragraph(Text(
                        "Put t=sqrt(epsilon) and q=tz. The normalized quotient Q(epsilon,tz)/t "
                        + "equals S(t,z)=|z(1+tz)(2-tz)|/[2(z^2(1+t^2(tz-1))+2)]. "
                        + "The limiting profile is L(z)=|z|/(z^2+2). If t>=0, R>=0, |z|<=R, "
                        + "tR<=1 and t^2<=1/4, then |S(t,z)-L(z)| is at most "
                        + "(tR^2+t^2R^3)/4+R^3t^2(1+tR)/4. For fixed R this bound tends to "
                        + "zero as t tends to zero, giving uniform convergence on bounded intervals.")),
                    Paragraph(Text(
                        "The rescaled physical domain is -1/t<=z<=3/t. If 0<epsilon<=1/4, "
                        + "R>0 and |z|>=R within this domain, the normalized quotient is at most 4/R. "
                        + "Taking R=32 makes this tail bound 1/8, strictly below the maximum "
                        + "1/(2sqrt(2)) of L. The point z=sqrt(2) attains that limiting maximum "
                        + "and belongs to the rescaled domain for all sufficiently small positive "
                        + "epsilon. The bounded-interval estimate and tail bound give the upper "
                        + "limit bound, while this realized point gives the lower limit bound.")),
                    Paragraph(Text(
                        "The definitions chordGain, gainValues, lowerGain and upperGain use the "
                        + "actual sensor chord divided by the Euclidean chord of circleState, with "
                        + "all pairs of distinct physical states included. The identity chord_gain_sq "
                        + "gives chordGain^2=P(epsilon,q)/Z, where "
                        + "P(epsilon,q)=q^2(1+epsilon(q-1))+2epsilon. For "
                        + "0<epsilon<=1/2 and -1<=q<=3, the coefficient "
                        + "1+epsilon(q-1) is nonnegative, so P>=2epsilon. The value q=0 is "
                        + "realized by a third-turn chord and attains equality. Taking the infimum "
                        + "therefore gives lowerGain^2=2epsilon/(9+20epsilon).")),
                    Paragraph(Text(
                        "On the same parameter range, q^2<=9 and "
                        + "1+epsilon(q-1)<=1+2epsilon give P<=9+20epsilon. Thus every physical "
                        + "chord gain is at most one. Differentiating each cosine-sine pair gives "
                        + "squared speed sum_i a_i^2 k_i^2=(4epsilon+9+16epsilon)/Z=1 "
                        + "at every phase. This derivative normalization requires only epsilon>0, "
                        + "so it holds on the entire positive parameter range. The global upper "
                        + "chord bound here uses epsilon<=1/2. The physical circle also has unit "
                        + "speed. The quotient "
                        + "of their short-chord lengths tends to one as d tends to zero from above. "
                        + "More explicitly, coordinate differentiation followed by the linear toLp "
                        + "map gives the derivative in the six-dimensional Euclidean space; "
                        + "sin^2+cos^2=1 reduces its norm square to the displayed budget at every phi. "
                        + "The one-sided slope-limit law at phase zero applies separately to sensor "
                        + "and circleState, and the denominator limit is one, so "
                        + "chordGain(epsilon,d,0) tends to one. These short physical states are "
                        + "eventually distinct. The gainValues set is nonempty and bounded above "
                        + "by one, while each short-chord gain lies below its supremum. Passing to "
                        + "the limit gives one<=upperGain; the uniform bound gives upperGain<=1. "
                        + "Thus for every 0<epsilon<=1/2, every phase has unit derivative norm "
                        + "and the actual sSup of all physical chord gains equals one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixdimensionalsharpgeometry-rank-defect-lower-gain-limit"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.actual_rank_defect_lower_gain_limit"),
                H("Rank defect relative to the least physical chord gain"),
                StatementSource.FromAuthor(RankDefectGainLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here actualRank retains the infimum of the actual two-delay Frobenius "
                        + "norm squared divided by the actual Euclidean operator norm squared, "
                        + "at the fixed delay pi/6. The lowerGain in the denominator is the "
                        + "infimum of the sensor-to-circle chord norm ratio over all distinct "
                        + "physical state pairs. The limit is through strictly positive epsilon.")),
                    Paragraph(Text(
                        "The correlation maximum characterization gives "
                        + "2-actualRank=2actualEta/(1+actualEta) for 0<epsilon<=1/2. "
                        + "The established actual_eta_scaled_limit and sqrt(epsilon)->0 imply "
                        + "actualEta->0. Using sqrt(epsilon/2)=sqrt(epsilon)/sqrt(2), "
                        + "actual_rank_defect_scaled_limit gives "
                        + "(2-actualRank)/sqrt(epsilon/2)->1. The sharp lower gain formula "
                        + "gives lowerGain/sqrt(epsilon)=sqrt(2/(9+20epsilon)), "
                        + "which tends to sqrt(2)/3. Dividing these limits and the constant "
                        + "sqrt(2) yields the stated value 3/2.")),
                    Paragraph(Text(
                        "The minimum of three frequency pairs and nonattainment of rank two "
                        + "for every finite injective harmonic family are separate assertions. "
                        + "Neither assertion follows from this fixed six-coordinate family "
                        + "and its small-epsilon asymptotics."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("The weighted observation experiment"), Blocks(
                Paragraph(Text(
                    "This application uses the existing six-coordinate sensor and finite-product Gaussian laws. Fix "
                    + "epsilon>0, an arbitrary finite index set J (possibly empty), arbitrary real weights w_j and delays "
                    + "t_j, and sigma>0. Put phi_false=0 and phi_true=2pi/3. With K=Fin 3 x Fin 2 and B=EuclideanSpace R K, "
                    + "define s_b(j)=w_j sensor(epsilon,phi_b-t_j). Thus the three cosine-sine pairs retain frequencies 2, "
                    + "3 and 4 and amplitudes sqrt(epsilon)/sqrt(9+20epsilon), 1/sqrt(9+20epsilon), "
                    + "sqrt(epsilon)/sqrt(9+20epsilon). The weights may be negative or zero; neither the delays nor the "
                    + "weights require normalization. The Gaussian argument imposes no upper bound on epsilon, so the "
                    + "restriction epsilon<=1/2 used for the sharp chord bounds above is not an assumption here.")),
                Paragraph(Text(
                    "Let Omega be a measurable space and let mu_b be a probability measure for each label b in Bool. For "
                    + "each j, let xi_bj:Omega -> B be mu_b-almost-everywhere measurable. Assume, separately for each b, "
                    + "that the family (xi_bj)_j is independent and that every component has law "
                    + "G_sigma=multivariateGaussian(0,sigma^2 I_K). These are real centered isotropic six-dimensional "
                    + "noises. Define the actual random observation Y_b(omega)(j)=s_b(j)+xi_bj(omega) and its law "
                    + "P_b=(mu_b).map(Y_b) on O=J -> B. Noise is added AFTER the signed weight multiplies the signal: its "
                    + "covariance is sigma^2 I_K even when w_j=0. In particular, this is not the model w_j(sensor+xi_bj). "
                    + "No independence, equality of samples or coupling between the two labels is assumed.")),
                Paragraph(Text(
                    "Write N_block=Measure.pi(j -> G_sigma). Independence and the component laws imply the actual joint "
                    + "identity (mu_b).map(omega -> (j -> xi_bj(omega)))=N_block by iIndepFun.map_fun_eq_pi_map. "
                    + "Consequently P_b=N_block.map(z -> s_b+z), using aemeasurable_pi_lambda and "
                    + "AEMeasurable.map_map_of_aemeasurable. Thus the product noise law is derived from the stated random "
                    + "variables; it is not an additional desired-law premise.")))),
            new DocumentBlock.Section(H("The actual flattening and its inverse"), Blocks(
                Paragraph(Text(
                    "Fix the coordinate bijection r:Fin 6 -> K characterized by r(2i+k)=(i,k), for i in Fin 3 and k in "
                    + "Fin 2. Set V=EuclideanSpace R (J x Fin 6). Define A:O -> V by (A y)(j,l)=y(j)(r(l)), with the "
                    + "Euclidean toLp constructor on the output, and Ainv:V -> O by (Ainv x)(j)(k)=x(j,r^{-1}(k)), again "
                    + "using toLp for each B-valued block. These are the actual coordinate maps, with Ainv composed with A "
                    + "equal to id_O and A composed with Ainv equal to id_V. Coordinatewise addition and scalar "
                    + "multiplication show linearity. Finite coordinate evaluation and the toLp maps show continuity in "
                    + "both directions; hence both maps are measurable and give a continuous linear equivalence O equivL[R] "
                    + "V.")),
                Paragraph(Text(
                    "The usual Pi norm on O is the maximum of the block Euclidean norms, whereas the norm on V is the "
                    + "square root of the sum of all squared coordinates. The displayed equivalence is not asserted to be "
                    + "an isometry for those norms. The finite reindexing r merely identifies the sensor owner's K=Fin 3 x "
                    + "Fin 2 with Fin 6: before that reindexing the same flattening has target EuclideanSpace R (J x K) and "
                    + "coordinates (j,k) -> y(j)(k). Thus it preserves the actual sensor coordinates and fixes exactly "
                    + "which six-coordinate convention is used.")),
                Paragraph(Text(
                    "Define m_b=A(s_b), explicitly m_b(j,l)=w_j sensor(epsilon,phi_b-t_j)(r(l)); set "
                    + "N=multivariateGaussian(0,sigma^2 I_(J x Fin 6)) and Q_b=multivariateGaussian(m_b,sigma^2 I_(J x Fin "
                    + "6)). The identities to be obtained are N_block.map(A)=N, P_b.map(A)=Q_b, Q_b=N.map(x -> m_b+x), and "
                    + "Q_b.map(Ainv)=P_b. The covariance sigma^2 I is on all 6|J| flattened coordinates, independently of "
                    + "the signed weights.")))),
            new DocumentBlock.Section(H("Deriving the Gaussian law from scalar products"), Blocks(
                Paragraph(Text(
                    "For any finite coordinate type L, let R_L=Measure.pi(l -> gaussianReal(0,1)), the product of scalar "
                    + "standard Gaussian probability measures. The affine definition of "
                    + "ProbabilityTheory.multivariateGaussian is the pushforward of stdGaussian by x -> "
                    + "m+toEuclideanCLM(CFC.sqrt(S))x. Since sigma>=0, Matrix.PosSemidef.one.smul makes sigma I positive "
                    + "semidefinite, and CFC.sqrt_mul_self applied to (sigma I)(sigma I)=sigma^2 I gives CFC.sqrt(sigma^2 "
                    + "I)=sigma I. ProbabilityTheory.map_pi_eq_stdGaussian then yields multivariateGaussian(m,sigma^2 "
                    + "I_L)=R_L.map(u -> m+sigma toLp(u)). This uses the positive matrix square root and the affine "
                    + "definition, with no added orthogonality assumption.")),
                Paragraph(Text(
                    "Apply this identity first with L=K and m=0. Measure.pi_map_pi says that N_block is the pushforward "
                    + "of T=Measure.pi(j -> R_K) by u -> (j -> sigma toLp(u(j))). The coordinate rearrangement "
                    + "U(u)(j,l)=u(j)(r(l)) sends T to R_(J x Fin 6). To see the actual law equality, take arbitrary "
                    + "measurable coordinate sets a_(j,l). The preimage of their product rectangle is the nested rectangle "
                    + "whose j-th factor has k-th set a_(j,r^{-1}(k)). Measure.pi_pi computes its mass as product_j "
                    + "product_k gaussianReal(0,1)(a_(j,r^{-1}(k))). Reindex the inner finite product by r and use "
                    + "Finset.prod_product to obtain product_(j,l) gaussianReal(0,1)(a_(j,l)). Measure.pi_eq identifies the "
                    + "measures from these rectangle values. This argument also covers the empty product.")),
                Paragraph(Text(
                    "The coordinate identity A(j -> sigma toLp(u(j)))=sigma toLp(U(u)) and Measure.map_map now give "
                    + "N_block.map(A)=R_(J x Fin 6).map(v -> sigma toLp(v))=N. With the same scalar-product formula at "
                    + "m=m_b, translation gives N.map(x -> m_b+x)=Q_b. Linearity gives A(s_b+z)=m_b+A(z), so the already "
                    + "derived P_b=N_block.map(z -> s_b+z) implies P_b.map(A)=Q_b. Finally Measure.map_map and Ainv "
                    + "composed with A=id_O give Q_b.map(Ainv)=P_b. In particular, both directions concern the original "
                    + "observation law, rather than a substituted Gaussian experiment.")))),
            new DocumentBlock.Section(H("Every measurable classifier and the empty experiment"), Blocks(
                Paragraph(Text(
                    "For every measurable classifier delta:O -> Bool, the transported classifier delta composed with Ainv "
                    + "is measurable. For each true label b and each event label c in Bool, Measure.map_apply applied to "
                    + "Q_b.map(Ainv)=P_b gives P_b({y | delta(y)=c})=Q_b({x | delta(Ainv(x))=c}) as an equality in ENNReal. "
                    + "Applying ENNReal.toReal gives the real-probability equality (P_b).real({y | "
                    + "delta(y)=c})=(Q_b).real({x | delta(Ainv(x))=c}). All these measures are probabilities, so these "
                    + "event values are finite.")),
                Paragraph(Text(
                    "Conversely, for every measurable h:V -> Bool, h composed with A is measurable and, for every b,c in "
                    + "Bool, P_b({y | h(A(y))=c})=Q_b({x | h(x)=c}) in ENNReal, with (P_b).real({y | "
                    + "h(A(y))=c})=(Q_b).real({x | h(x)=c}) after ENNReal.toReal. This follows from P_b.map(A)=Q_b and "
                    + "Measure.map_apply. Both assertions quantify over all measurable classifiers and both Boolean events; "
                    + "they are not restricted to threshold rules.")),
                Paragraph(Text(
                    "If J is empty, O and V each have only their zero vector and s_b=m_b=0. Measure.pi_of_empty gives "
                    + "N_block=Measure.dirac(0); its translated pushforward gives the actual P_b=Measure.dirac(0), and "
                    + "flattening gives the actual Q_b=Measure.dirac(0). Thus the inverse maps, Gaussian law "
                    + "identifications and both classifier probability equalities include the zero-dimensional experiment "
                    + "without a nonempty-index hypothesis.")),
                Paragraph(Text(
                    "The parameter binding is sigma to the positive noise scale, s to the actual weighted harmonic means "
                    + "s_b, mu to the two original per-label probability measures, and xi to their independent B-valued "
                    + "noise coordinates. The sensor definition belongs to SixDimensionalSharpGeometry; the affine "
                    + "Gaussian, independence, finite-product and pushforward suppliers are existing public Mathlib results "
                    + "at pin db584cd6d46c92f209a44c0f1c829460d327499d, recorded in lake-manifest.json. This is an "
                    + "application of those results, with the coordinate reindexing written explicitly, not an additional "
                    + "Lean theorem or a new library result. GaussianObservationLaw separately owns its posterior, "
                    + "likelihood and information statement; that statement is not needed as a premise here.")),
                Paragraph(Text(
                    "This application establishes the block-noise experiment, its actual Gaussian flattening and exact "
                    + "all-classifier event-probability transport. It does not establish a scalar score/residual "
                    + "decomposition, a reconstruction kernel, an optimized global risk formula, an energy or quantile "
                    + "bound, a design cap or an asymptotic risk law. Those would require their own assumptions and "
                    + "arguments beyond the law and probability identities given here.")))),
            new DocumentBlock.Section(H("The actual score and orthogonal residual"), Blocks(
                Paragraph(Text(
                    "Continue the same weighted observation experiment with 0<epsilon<=1/2, sigma>0, arbitrary finite J, "
                    + "signed real weights w_j and real delays t_j. The preceding block-noise and flattening argument supplies "
                    + "C01/C02; the following score and reconstruction argument supplies C03/C04. Use its actual flattened means "
                    + "m_b=A(s_b), covariance S=sigma^2 I, centered law N=multivariateGaussian(0,S), and observation laws "
                    + "Q_b=multivariateGaussian(m_b,S)=N.map(x -> m_b+x). All formulas use the same Fin 6 reindexing of K=Fin 3 "
                    + "x Fin 2 already specified; equivalently they can be written in EuclideanSpace R (J x K) before "
                    + "reindexing. The weights still multiply only the sensor signal, and the isotropic noise is added "
                    + "afterwards. No target score law, residual law, independence or support statement is an extra hypothesis.")),
                Paragraph(Text(
                    "Set d=m_true-m_false, D=norm(d), and c=(m_false+m_true)/2. For D>0 define u=D^{-1} d, "
                    + "alpha(x)=inner(u,x), and P_perp(x)=x-alpha(x)u. Thus alpha=innerSL R u and P_perp=id-alpha.smulRight(u) "
                    + "are continuous linear maps. Put beta_false=-D/2, beta_true=D/2, lambda_b=gaussianReal(beta_b,sigma^2), "
                    + "and nu=N.map(P_perp); sigma^2 is viewed as a nonnegative real parameter in gaussianReal. Define the "
                    + "actual score T(y)=alpha(y-c), residual R(y)=P_perp(y-c), F(y)=(T(y),R(y)), and G(r,z)=c+r u+z. These maps "
                    + "are measurable. The product target uses this particular pushforward nu of the actual centered noise.")),
                Paragraph(Text(
                    "Normalization gives norm(u)=1, alpha(u)=1 and D u=d, whence m_b-c=beta_b u. Directly from the formula for "
                    + "P_perp, alpha(P_perp x)=0, P_perp(u)=0, P_perp(P_perp x)=P_perp x, and inner(v,P_perp x)=inner(P_perp "
                    + "v,x). Its range equals ker(alpha): the first identity gives one inclusion, and alpha(z)=0 implies "
                    + "P_perp(z)=z for the other. These identities use D>0 only to obtain the unit direction; no unit vector is "
                    + "asserted when D=0.")))),
            new DocumentBlock.Section(H("Joint Gaussianity, independence and the product law"), Blocks(
                Paragraph(Text(
                    "On the single probability space (V,N), start with the actual pair x -> (alpha(x),P_perp(x)). "
                    + "IsGaussian.hasGaussianLaw_id and HasGaussianLaw.map_fun applied to the continuous linear map "
                    + "alpha.prod(P_perp) give its joint Gaussian law. Matrix.PosSemidef.one.smul makes S positive semidefinite, "
                    + "and covarianceBilin_multivariateGaussian gives covarianceBilin(N)(v,w)=sigma^2 inner(v,w). For every real "
                    + "a and vector v, self-adjointness of P_perp therefore gives "
                    + "Cov_N(inner(a,alpha(x)),inner(v,P_perp(x)))=sigma^2 inner(a u,P_perp(v))=sigma^2 a alpha(P_perp(v))=0. "
                    + "This checks all scalar cross-covariances. HasGaussianLaw.indepFun_of_covariance_inner now derives "
                    + "independence of alpha and P_perp from their common joint Gaussian law; separate Gaussian marginals alone "
                    + "would not supply that inference.")),
                Paragraph(Text(
                    "The centered score has integral zero: commute alpha with integration and use "
                    + "integral_id_multivariateGaussian. Its variance is covarianceBilin(N)(u,u)=sigma^2 because norm(u)=1. For "
                    + "each b, translation by m_b sends N to Q_b and F(m_b+x)=(beta_b+alpha(x),P_perp(x)). Hence under Q_b the "
                    + "actual T is Gaussian with expectation beta_b and variance sigma^2. HasGaussianLaw.map_eq_gaussianReal "
                    + "identifies Q_b.map(T)=lambda_b. Independence survives adding beta_b to the first component by "
                    + "IndepFun.comp; IndepFun.map_prod_eq_prod_map_map then gives Q_b.map(F)=lambda_b.prod(nu). The second "
                    + "component of the same translation identity gives Q_b.map(R)=nu for both labels. Thus the label "
                    + "information appears only in the score mean; the common residual and product law are derived from the "
                    + "original Q_b.")),
                Paragraph(Text(
                    "The identity alpha(P_perp x)=0 also proves nu(ker(alpha))=1 by Measure.map_apply, since the preimage of "
                    + "that closed kernel is all of V and N has mass one. The residual is allowed to be singular on the ambient "
                    + "space: no invertible residual covariance or ambient Lebesgue density is assumed. Both labels use exactly "
                    + "N.map(P_perp), with its full mass on the same orthogonal hyperplane.")))),
            new DocumentBlock.Section(H("Reconstruction and one label-independent Markov kernel"), Blocks(
                Paragraph(Text(
                    "For every y in V, cancellation in c+alpha(y-c)u+((y-c)-alpha(y-c)u) gives the GLOBAL identity G(F(y))=y. "
                    + "In the other direction, for every real r and every z with alpha(z)=0, alpha(r u+z)=r and P_perp(r u+z)=z, "
                    + "so F(G(r,z))=(r,z). This second identity is asserted on R x ker(alpha), a set of full lambda_b.prod(nu) "
                    + "measure, rather than on all of R x V. Applying Measure.map_map to Q_b.map(F)=lambda_b.prod(nu) and the "
                    + "global G-after-F identity gives the exact reverse law (lambda_b.prod(nu)).map(G)=Q_b for each b.")),
                Paragraph(Text(
                    "Define kappa(r)=nu.map(z -> c+r u+z), using the SAME c, u and nu for both labels. A concrete measurable "
                    + "kernel is ((Kernel.id : Kernel R R) x_kernel Kernel.const R nu).map(G); Kernel.prod_apply, "
                    + "Kernel.id_apply, Kernel.const_apply and Measure.dirac_prod give the displayed value at every r. Since nu "
                    + "is a probability measure and G is measurable, Kernel.IsMarkovKernel.map makes kappa a Markov kernel. "
                    + "There is no label argument in its definition, and no desired conditional law is assumed.")),
                Paragraph(Text(
                    "To obtain the actual score-observation joint law, set H(r,z)=(r,G(r,z)). For every measurable E in R x V, "
                    + "Measure.compProd_apply integrates kappa(r)({y | (r,y) in E}) against lambda_b. Substitute the explicit "
                    + "kappa and use Measure.map_apply and Measure.prod_apply: this integral is (lambda_b.prod(nu))(H^{-1}(E)). "
                    + "Consequently lambda_b compProd kappa=(lambda_b.prod(nu)).map(H). Substituting Q_b.map(F) for the product "
                    + "and using H(F(y))=(T(y),y), by the global inverse, proves Q_b.map(y -> (T(y),y))=lambda_b compProd kappa. "
                    + "This identifies the true joint law, beyond a reconstruction marginal. Taking its second marginal yields "
                    + "(lambda_b compProd kappa).map(Prod.snd)=Q_b. Finally F(G(r,z))=(r,z) on the full-nu kernel gives "
                    + "(kappa(r)).map(T)=Measure.dirac(r) for EVERY real r, including values outside any chosen "
                    + "almost-everywhere version.")))),
            new DocumentBlock.Section(H("Coincident means, empty designs and remaining limits"), Blocks(
                Paragraph(Text(
                    "If D=0, norm(d)=0 implies m_true=m_false, hence Q_true=Q_false. Use the constant score T_0(y)=0 and the "
                    + "constant Markov kernel kappa_0(r)=Q_false for every real r. Then Q_b.map(T_0)=Measure.dirac(0), and "
                    + "Measure.compProd_const together with Measure.dirac_prod gives Q_b.map(y -> (0,y))=Measure.dirac(0) "
                    + "compProd kappa_0. Its second marginal is Q_b. This branch uses neither division by D nor a unit "
                    + "direction, and its score variance is zero, not sigma^2. The nondegenerate identity "
                    + "(kappa(r)).map(T)=dirac(r) is not extended to every r for this constant-score kernel.")),
                Paragraph(Text(
                    "If J is empty, the flattened coordinate space has only its zero vector. Thus m_b=0, D=0, "
                    + "N=Measure.dirac(0) and Q_b=Measure.dirac(0); the original P_b is also the zero Dirac law by the preceding "
                    + "flattening argument. Every probability measure on that singleton is the zero Dirac law, so this is the "
                    + "actual empty experiment, not a limiting positive-dimensional model. Arbitrary zero weights and coincident "
                    + "means are likewise handled by the D=0 branch without assuming J nonempty.")),
                Paragraph(Text(
                    "The sensor and its weighted means remain those of SixDimensionalSharpGeometry. The Gaussian mapping, "
                    + "covariance, independence, pushforward and kernel arguments apply the existing public Mathlib suppliers "
                    + "named above, at pin db584cd6d46c92f209a44c0f1c829460d327499d. Together with C01/C02, these identities "
                    + "retain the original C03/C04 score, common residual, reverse law and shared Markov joint law as an "
                    + "application of existing results. Beyond these C01/C04 identities, optimized global risk, energy or quantile "
                    + "bounds, design caps and asymptotic risk laws require further arguments; C05/C06 is supplied below. No conclusion "
                    + "about completion of the parent problem follows.")))),
            new DocumentBlock.Section(H("Actual equal-prior risk over every original classifier"), Blocks(
                Paragraph(Text(
                    "Continue exactly the same experiment: 0<epsilon<=1/2, sigma>0, arbitrary finite J (including empty J), real "
                    + "signed weights w_j and arbitrary real delays t_j. The two phases are phi_false=0 and phi_true=2pi/3. The "
                    + "original observation is Y_b(omega)(j)=s_b(j)+xi_bj(omega), where s_b(j)=w_j sensor(epsilon,phi_b-t_j). For "
                    + "each b the base measure mu_b is a probability measure, each xi_bj is AE-measurable, the family is "
                    + "independent under that same mu_b, and each coordinate noise has law multivariateGaussian(0,sigma^2 I_K), "
                    + "K=Fin 3 x Fin 2. No relation between the two underlying label spaces is used. These are the original noise "
                    + "assumptions: weights multiply the signal before the independent noise is added. In particular the noise "
                    + "covariance is sigma^2 I, not a covariance multiplied by w_j^2.")),
                Paragraph(Text(
                    "Write P_b=(mu_b).map(Y_b) on O=J -> EuclideanSpace R K, m_b=A(s_b), Q_b=multivariateGaussian(m_b,sigma^2 I), "
                    + "and D=norm(m_true-m_false). The preceding coordinate equivalence gives P_b.map(A)=Q_b and Q_b.map(Ainv)=P_b. "
                    + "For EVERY measurable deterministic delta:O -> Bool define its actual equal-prior error risk by "
                    + "Risk(delta)=[P_false.real({y | delta(y)=true})+P_true.real({y | delta(y)=false})]/2. Here measure.real is "
                    + "ENNReal.toReal of the event measure; both laws are probabilities, so these values are finite. Equivalently "
                    + "Risk(delta)=[integral_O 1_{delta=true}(y) dP_false(y)+integral_O 1_{delta=false}(y) dP_true(y)]/2. The two "
                    + "real indicator functions are measurable, take values in [0,1], and are integrable against the corresponding "
                    + "probability measures. Thus 0<=Risk(delta)<=1. The infimum below is taken over this original class of "
                    + "measurable deterministic rules on O.")),
                Paragraph(Text(
                    "For D>0 keep the already derived c=(m_false+m_true)/2, u=(m_true-m_false)/D, alpha(x)=inner(u,x), "
                    + "P_perp(x)=x-alpha(x)u, T(x)=alpha(x-c), G(q,z)=c+q u+z, N=multivariateGaussian(0,sigma^2 I), "
                    + "nu=N.map(P_perp), and lambda_b=gaussianReal(beta_b,sigma^2), with beta_false=-D/2 and beta_true=D/2. In the "
                    + "following formulas q is a real score variable, unrelated to the earlier chord parameter. The C03/C04 "
                    + "argument proves that nu is a probability measure, nu(ker(alpha))=1, Q_b.map(F)=lambda_b.prod(nu), and "
                    + "(lambda_b.prod(nu)).map(G)=Q_b. Composing the last identity with Ainv gives (lambda_b.prod(nu)).map(Ainv "
                    + "composed with G)=P_b. These are consequences of the actual observation model. No product law, support, score "
                    + "distribution or score/residual independence premise is added.")))),
            new DocumentBlock.Section(H("Fubini reduction of the actual deterministic-rule risk"), Blocks(
                Paragraph(Text(
                    "For a fixed measurable delta:O -> Bool put a_delta(q,z)=1 if delta(Ainv(G(q,z)))=true and 0 otherwise, and "
                    + "r_delta(q)=integral_V a_delta(q,z) dnu(z). Composition of the measurable reconstruction, Ainv, delta and the "
                    + "Boolean indicator shows that a_delta is jointly measurable. For every q, both a_delta(q,.) and "
                    + "1-a_delta(q,.) are measurable and bounded between zero and one. They are therefore integrable against nu. "
                    + "Since nu(V)=1, monotonicity of the integral gives 0<=r_delta(q)<=1 for every q, and integral_V "
                    + "(1-a_delta(q,z)) dnu(z)=1-r_delta(q).")),
                Paragraph(Text(
                    "Parameter integration of the strongly measurable real-valued function a_delta gives a measurable r_delta. "
                    + "For each b, a_delta and 1-a_delta are integrable on lambda_b.prod(nu), because they are bounded measurable "
                    + "functions on a probability space. Likewise r_delta and 1-r_delta are integrable against lambda_b. All these "
                    + "assertions include every score q for the section integrals; they do not require a density for nu. The actual "
                    + "nu can be singular as a measure on V.")),
                Paragraph(Text(
                    "Apply the pushforward integral formula to (lambda_b.prod(nu)).map(Ainv composed with G)=P_b and to the "
                    + "measurable event indicators. It gives P_b.real({delta=true})=integral_(R x V) a_delta d(lambda_b.prod(nu)) "
                    + "and P_b.real({delta=false})=integral_(R x V) (1-a_delta) d(lambda_b.prod(nu)). Fubini applies to the "
                    + "integrable functions just checked. Consequently Risk(delta)=[integral_R r_delta(q) "
                    + "dlambda_false(q)+integral_R (1-r_delta(q)) dlambda_true(q)]/2. This is an equality for each original "
                    + "deterministic classifier, not a replacement of that classifier class by randomized Markov rules. The "
                    + "function r_delta is only the average of its actual indicator over the derived common residual.")))),
            new DocumentBlock.Section(H("Density domination and the lower bound for all rules"), Blocks(
                Paragraph(Text(
                    "View v=sigma^2 as a strictly positive nonnegative-real variance. With respect to Lebesgue measure dq on R "
                    + "define f_minus(q)=gaussianPDFReal(-D/2,v,q) and f_plus(q)=gaussianPDFReal(D/2,v,q). Explicitly "
                    + "f_minus(q)=exp(-(q+D/2)^2/(2sigma^2))/sqrt(2pi sigma^2), and f_plus(q)=exp(-(q-D/2)^2/(2sigma^2))/sqrt(2pi "
                    + "sigma^2). These densities are measurable, nonnegative and integrable, with integral one. Since "
                    + "0<=r_delta<=1, the products r_delta f_minus and (1-r_delta) f_plus are measurable, nonnegative, and "
                    + "dominated respectively by f_minus and f_plus; hence both are Lebesgue integrable. Changing from the Gaussian "
                    + "measures to their densities and adding integrals therefore gives Risk(delta)=(1/2) integral_R "
                    + "[r_delta(q)f_minus(q)+(1-r_delta(q))f_plus(q)] dq.")),
                Paragraph(Text(
                    "Set h(q)=min(f_minus(q),f_plus(q)) and L=(1/2) integral_R h(q) dq. The measurable function h is integrable "
                    + "because 0<=h<=f_minus. Pointwise, for any 0<=r<=1, r f_minus+(1-r)f_plus-h=r(f_minus-h)+(1-r)(f_plus-h)>=0. "
                    + "Substituting r_delta(q) and applying integral monotonicity yields L<=Risk(delta) for EVERY measurable "
                    + "deterministic delta on O. The scalar inequality works for every measurable [0,1]-valued r, but the "
                    + "conclusion here concerns the original all-classifier risk through its proved integral identity.")),
                Paragraph(Text(
                    "For D>0 the normalizing density constant and 2sigma^2 are positive. The exponential is strictly increasing, "
                    + "and (q+D/2)^2-(q-D/2)^2=2qD. Hence f_minus(q)<=f_plus(q) if and only if q>=0. At q=0 the two densities "
                    + "agree. Thus q_star(q)=1 for q>=0 and 0 for q<0 satisfies q_star f_minus+(1-q_star)f_plus=min(f_minus,f_plus) "
                    + "at every q, including the midpoint tie. Integrating proves that the scalar lower bound L is attained by this "
                    + "threshold average.")))),
            new DocumentBlock.Section(H("Attainment by a measurable rule on the original observation space"), Blocks(
                Paragraph(Text(
                    "Define delta_star(y)=true exactly when T(A(y))>=0, choosing true at a tie. The set {y | 0<=T(A(y))} is "
                    + "closed because T and A are continuous, so delta_star:O -> Bool is measurable. This rule is deterministic and "
                    + "acts on the actual original observation y. It has been defined using only the model parameters, without "
                    + "introducing extra residual randomness.")),
                Paragraph(Text(
                    "For EVERY q in R and every z in ker(alpha), A(Ainv(G(q,z)))=G(q,z) and T(G(q,z))=q. Since nu(ker(alpha))=1, "
                    + "a_delta_star(q,z)=q_star(q) for nu-almost every z. Integrating this equality against the probability measure "
                    + "nu gives r_delta_star(q)=q_star(q) for every real q. In particular r_delta_star(0)=1 with the chosen tie "
                    + "convention. The risk identity then gives Risk(delta_star)=L. Combining this equality with the all-rule lower "
                    + "bound proves Risk(delta_star)<=Risk(delta) for every measurable delta:O -> Bool. The support property needed "
                    + "for this step was derived from nu=N.map(P_perp), including its possible singularity; it was not imposed on "
                    + "an arbitrary auxiliary law.")))),
            new DocumentBlock.Section(H("Gaussian tails and the attained literal real infimum"), Blocks(
                Paragraph(Text(
                    "Define Phi(x)=cdf(gaussianReal(0,1),x)=gaussianReal(0,1).real((-infinity,x]). To evaluate L, first push "
                    + "gaussianReal(0,1) forward by z -> m+sigma z. The public Gaussian multiplication and translation laws give "
                    + "gaussianReal(m,sigma^2). Because sigma>0, the preimage of (-infinity,a] is (-infinity,(a-m)/sigma], so "
                    + "gaussianReal(m,sigma^2).real((-infinity,a])=Phi((a-m)/sigma). The positive variance Gaussian has no atoms. "
                    + "The same equality therefore holds for (-infinity,a), without a boundary mass at a.")),
                Paragraph(Text(
                    "Reflection z -> -z preserves gaussianReal(0,1). Applying that pushforward identity to half-lines, using the "
                    + "zero mass of a singleton and the probability complement identity, gives Phi(-x)=1-Phi(x); at x=0 this yields "
                    + "Phi(0)=1/2. For the threshold rule, the false-label error is "
                    + "lambda_false.real([0,infinity))=1-Phi(D/(2sigma))=Phi(-D/(2sigma)). The true-label error is "
                    + "lambda_true.real((-infinity,0))=Phi(-D/(2sigma)). Thus L=Risk(delta_star)=Phi(-D/(2sigma)). The endpoint "
                    + "convention agrees with the deterministic tie choice, and atomlessness makes the displayed tail calculation "
                    + "exact.")),
                Paragraph(Text(
                    "Let S_Risk={q in R | there exists delta:O -> Bool with Measurable(delta) and Risk(delta)=q}. The measurable "
                    + "rule delta_star supplies Risk(delta_star) in S_Risk, so the set is nonempty. Every element is at least L by "
                    + "the all-rule bound (and is nonnegative from the original indicator formula), so S_Risk is bounded below. "
                    + "Since Risk(delta_star)=L, L is an attained least element of S_Risk. The conditionally complete real-order "
                    + "identity IsLeast.csInf_eq gives the literal equality sInf {q:R | exists delta:O -> Bool, Measurable(delta) "
                    + "and Risk(delta)=q}=Phi(-D/(2sigma)). This is the real sInf of the actual deterministic-rule risk set, "
                    + "together with an original-space rule attaining it.")))),
            new DocumentBlock.Section(H("Zero distance and empty designs in the same risk theorem"), Blocks(
                Paragraph(Text(
                    "If D=0, norm(m_true-m_false)=0 implies m_true=m_false, hence Q_true=Q_false. Applying Ainv to these "
                    + "identical laws gives P_true=P_false=P. For any measurable delta:O -> Bool the Boolean events {delta=true} "
                    + "and {delta=false} are measurable complements. Their P.real probabilities sum to one, so Risk(delta)=1/2 for "
                    + "every such delta. The constant-false classifier is measurable and attains 1/2. Therefore S_Risk is the "
                    + "singleton {1/2}, its literal real sInf is 1/2, and Phi(-D/(2sigma))=Phi(0)=1/2. This branch never divides by "
                    + "D and never requires a unit direction.")),
                Paragraph(Text(
                    "If J is empty, O and V are singletons, m_b=0 and D=0. The actual original P_b and flattened Q_b are the zero "
                    + "Dirac laws derived in C01/C02. Thus every original measurable classifier has risk 1/2, the constant rule "
                    + "attains it, and the real infimum is 1/2. All-zero weights and any other design with coincident means are covered by the D=0 argument. "
                    + "Arbitrary signed weights remain allowed in both branches, with the branch determined by D. Combining D=0 with D>0 (D is always a norm and nonnegative) proves for every "
                    + "admitted design that there exists a measurable deterministic delta_star on O attaining Phi(-D/(2sigma)), "
                    + "that this risk is no larger than that of any other measurable original classifier, and that the literal real "
                    + "sInf equals this value.")))),
            new DocumentBlock.Section(H("Parameter correspondence, existing suppliers and scope"), Blocks(
                Paragraph(Text(
                    "The correspondence is exact: epsilon and the two phases determine the same harmonic sensor, w and t "
                    + "determine its original means s_b, mu and xi determine its actual observation laws P_b, sigma is the positive "
                    + "post-weight noise scale, and sigma^2 is the variance parameter of gaussianReal. Flattening through the "
                    + "stated Fin 6 bijection identifies the formulas above with coordinates J x (Fin 3 x Fin 2); sums of squares, "
                    + "D, inner products, alpha and the risk are unchanged by this coordinate reindexing. The common residual is "
                    + "specifically N.map(P_perp), and reconstruction on O is specifically Ainv composed with G. In supplier "
                    + "formulas for a product integral, the first measure is lambda_b, the second is nu and the integrand is "
                    + "a_delta or 1-a_delta; in the Gaussian density formula the mean is -D/2 or D/2 and the variance is sigma^2. "
                    + "The order-theoretic supplier is applied to S_Risk and its attained least element.")),
                Paragraph(Text(
                    "The sensor is the existing definition in "
                    + "D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.lean; its observation "
                    + "and score laws are derived above using the existing public Gaussian suppliers. For the risk step, "
                    + "Mathlib/MeasureTheory/Function/L1Space/Integrable.lean supplies Integrable.of_mem_Icc. "
                    + "Mathlib/MeasureTheory/Integral/Prod.lean supplies StronglyMeasurable.integral_prod_right' and integral_prod. "
                    + "The Bochner integral files Mathlib/MeasureTheory/Integral/Bochner/Basic.lean and Set.lean supply "
                    + "integral_map_of_stronglyMeasurable, integral_indicator_one, integral_sub, integral_add and integral_mono. "
                    + "These are used on the actual bounded indicators and probability measures just identified.")),
                Paragraph(Text(
                    "At the same pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, "
                    + "Mathlib/Probability/Distributions/Gaussian/Real.lean supplies gaussianPDFReal, gaussianPDFReal_nonneg, "
                    + "measurable_gaussianPDFReal, integrable_gaussianPDFReal, integral_gaussianReal_eq_integral_smul, "
                    + "gaussianReal_map_const_mul, gaussianReal_map_const_add, gaussianReal_map_neg and "
                    + "nullSingletonClass_gaussianReal. Mathlib/Probability/CDF.lean supplies cdf_eq_real; "
                    + "Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean supplies Iio_ae_eq_Iic and Ioi_ae_eq_Ici; "
                    + "Mathlib/MeasureTheory/Measure/Real.lean supplies the real probability-complement identities. The real-order "
                    + "step uses IsLeast.csInf_eq from Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean. These source "
                    + "citations identify existing suppliers of the application, not new repository declarations.")),
                Paragraph(Text(
                    "This is the C05/C06 application of the existing results to the actual original harmonic-sensor experiment. "
                    + "Its indicator definitions, Fubini reduction, scalar Gaussian comparison, deterministic midpoint attainment "
                    + "and degenerate reductions introduce no new Lean declaration, theorem Describe, registration, frozen identity "
                    + "or claim of library novelty. C01/C04 and their original parameter scope remain as above. C07 and C09-C13, including "
                    + "quantile bounds, design caps and asymptotic risk laws, are not established by this risk calculation; "
                    + "the deterministic C08 energy identities follow below. No completion of the parent problem is claimed.")))),
            new DocumentBlock.Section(H("C08: exact energy of the original harmonic-sensor means"), Blocks(
                Paragraph(Text(
                    "Keep 0<epsilon<=1/2, sigma>0, every finite J including the empty type, arbitrary signed real weights w:J -> R and "
                    + "arbitrary real delays t:J -> R. Put Z=normalization(epsilon)=9+20epsilon>0, K=Fin 3 x Fin 2, B=EuclideanSpace R K, "
                    + "O=J -> B and V=EuclideanSpace R (J x K). The same actual sensor H= sensor(epsilon,.) has frequencies k=(2,3,4), "
                    + "amplitudes a=(sqrt(epsilon),1,sqrt(epsilon))/sqrt(Z), and coordinates H(phi)(i,0)=a_i cos(k_i phi), H(phi)(i,1)=a_i "
                    + "sin(k_i phi). These are the existing frequencies, amplitudes and pairedSensor definitions, with "
                    + "a_0^2=a_2^2=epsilon/Z and a_1^2=1/Z.")),
                Paragraph(Text(
                    "Use exactly the earlier flattening A:O -> V, A(y)=toLp 2 (p -> y(p.1)(p.2)). Set m_false=A(j -> w_j H(-t_j)), "
                    + "m_true=A(j -> w_j H(2pi/3-t_j)), d=m_true-m_false, D=norm(d), and E=sum_j w_j^2. In particular, for each Boolean b, "
                    + "A(j -> w_j H(phi_b-t_j)) is m_false or m_true according to b, with phi_false=0 and phi_true=2pi/3. These are the "
                    + "means of the preceding actual experiment. The deterministic calculation below needs no further noise assumption; "
                    + "sigma remains its positive post-weight noise scale and does not enter E or D. All norms and sums used below are "
                    + "Euclidean in B or V. No identification of the Pi-space norm on O with the Euclidean norm of its flattening is used.")))),
            new DocumentBlock.Section(H("Third-turn chord, rotation invariance and the Euclidean energy sum"), Blocks(
                Paragraph(Text(
                    "For the ith two-coordinate block, shifting a phase by -t_j rotates that block through -k_i t_j. The same orthogonal "
                    + "rotation acts on both endpoints, so it preserves the block chord norm. Explicitly, "
                    + "(cos(alpha)-cos(beta))^2+(sin(alpha)-sin(beta))^2=4 sin((alpha-beta)/2)^2. Multiplying by a_i^2 and summing the "
                    + "three blocks gives norm(H(phi)-H(psi))^2=4 sum_i a_i^2 sin(k_i(phi-psi)/2)^2. With phi=2pi/3-t_j and psi=-t_j, their "
                    + "difference is exactly 2pi/3 for every delay. The three sine squares are sin(2pi/3)^2=3/4, sin(pi)^2=0 and "
                    + "sin(4pi/3)^2=3/4. Therefore each actual sensor chord has square "
                    + "4[(epsilon/Z)(3/4)+(1/Z)0+(epsilon/Z)(3/4)]=6epsilon/Z.")),
                Paragraph(Text(
                    "Equivalently, apply the existing six_chord_norm_sq to these actual endpoints. Their half-difference is pi/3, "
                    + "chordParameter=4cos(pi/3)^2-1=0, and chordPolynomial(epsilon,0)=2epsilon. The theorem therefore gives "
                    + "(4sin(pi/3)^2/Z)(2epsilon)=6epsilon/Z. This directly identifies the delay-independent coordinate calculation with "
                    + "the original owner theorem.")),
                Paragraph(Text(
                    "For any y:O, EuclideanSpace.real_norm_sq_eq and the finite-product sum identity give norm(A(y))^2=sum_(j,k) "
                    + "y(j)(k)^2=sum_j norm(y(j))^2. Coordinatewise distributivity gives d=A(j -> w_j [H(2pi/3-t_j)-H(-t_j)]). Thus "
                    + "D^2=sum_j norm(w_j [H(2pi/3-t_j)-H(-t_j)])^2=sum_j w_j^2 norm(H(2pi/3-t_j)-H(-t_j))^2. The scalar norm law is "
                    + "norm(w_j v)=abs(w_j) norm(v), and abs(w_j)^2=w_j^2, so this step includes negative as well as zero weights. Distinct "
                    + "j occupy distinct Euclidean blocks; no cross-block cancellation term occurs. Substituting the chord square and "
                    + "distributing the finite sum yields D^2=(6epsilon/Z)sum_j w_j^2=6epsilon E/(9+20epsilon).")))),
            new DocumentBlock.Section(H("The actual infimum gain and the positive square-root identities"), Blocks(
                Paragraph(Text(
                    "The lower gain is the existing physical infimum, not an introduced scalar surrogate: "
                    + "chordGain(epsilon,phi,psi)=norm(H(phi)-H(psi))/norm(circleState(phi)-circleState(psi)); gainValues(epsilon) contains "
                    + "these ratios for all phi,psi with distinct physical circle states; lowerGain(epsilon)=sInf(gainValues(epsilon)). The "
                    + "original lower_gain_eq_sqrt, with its existing proof body and the same hypotheses 0<epsilon<=1/2, gives "
                    + "lowerGain(epsilon)=sqrt(2epsilon/Z). Its argument bounds every actual chord gain below and attains the bound at a "
                    + "realized chordParameter of zero; it therefore identifies this actual infimum over physical states. The existing "
                    + "lower_gain_sq gives lowerGain(epsilon)^2=2epsilon/Z.")),
                Paragraph(Text(
                    "Because epsilon>0 and Z>0, lowerGain(epsilon)>0, in particular it is nonnegative. Also E>=0 as a sum of squares and "
                    + "D>=0 as a norm. Combining the exact energy square with lower_gain_sq gives D^2=3E lowerGain(epsilon)^2. The "
                    + "nonnegative square root of D^2 is D, so D=sqrt(6epsilon E/(9+20epsilon)). Both D and sqrt(3E) lowerGain(epsilon) are "
                    + "nonnegative and have equal squares, hence D=sqrt(3E) lowerGain(epsilon). The sign checks apply also at E=0 and "
                    + "require no division by E or D.")))),
            new DocumentBlock.Section(H("Zero energy, empty designs and the remaining scope"), Blocks(
                Paragraph(Text(
                    "Since 6epsilon/Z>0, the squared identity gives E=0 if and only if D=0. If E=0, norm(m_true-m_false)=0 and therefore "
                    + "m_true=m_false; conversely equal means give D=0 and hence E=0. All-zero weights are included. Signed weights remain "
                    + "arbitrary, but a negative weight does not itself make E or D vanish. If J is empty, its finite sum is zero and J x K "
                    + "has no coordinates: E=0, D=0 and both actual means are the zero vector. These conclusions use the same definitions "
                    + "and do not assume J is nonempty or pass to a positive-dimensional limit.")),
                Paragraph(Text(
                    "The supplier correspondence is precise: the epsilon in normalization, sensor, six_chord_norm_sq, lower_gain_eq_sqrt "
                    + "and lower_gain_sq is the experiment's epsilon; the two chord phases are 2pi/3-t_j and -t_j; the index in the "
                    + "Euclidean product sum is (j,k); and scalar multiplication uses the original signed w_j. These declarations are in "
                    + "D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry.lean, while "
                    + "PairedDelayGeometry.paired_chord_norm_sq in that same source gives the block sum. At Mathlib pin "
                    + "db584cd6d46c92f209a44c0f1c829460d327499d, Mathlib/Analysis/InnerProductSpace/PiL2.lean supplies "
                    + "EuclideanSpace.real_norm_sq_eq, the finite-product big-operator APIs supply Fintype.sum_prod_type and "
                    + "Finset.sum_mul, the normed scalar-action API supplies norm_smul, and Mathlib/Analysis/Real/Sqrt.lean supplies the "
                    + "nonnegative square-root identities. This is an application of these existing results; the exact gain formula is not "
                    + "claimed as new mathematics.")),
                Paragraph(Text(
                    "This establishes the original C08 energy identities and their zero and empty cases for the actual means, alongside "
                    + "the C01-C06 applications above. C07 and C09-C13, including the remaining quantile bounds, design caps and asymptotic "
                    + "risk laws, remain outside these conclusions. No completion of the parent problem is asserted.")))),
            new DocumentBlock.Section(H("C10/C11: energy thresholds and joint design optimization for the original experiment"), Blocks(
                Paragraph(Text(
                    "Retain the original telescope: J is any finite type, including the empty type, w:J -> R has arbitrary signed entries, and t:J -> R "
                    + "is an arbitrary fixed delay family. Assume 0<epsilon<=1/2, sigma>0 and 0<alpha<1/2. On the same measurable sample space Omega, each "
                    + "mu_b is a probability measure; each xi_b,j:Omega -> B is AEMeasurable for mu_b, the family xi_b is independent under mu_b, and "
                    + "(mu_b).map(xi_b,j)=multivariateGaussian(0,sigma^2 I) on B=EuclideanSpace R (Fin 3 x Fin 2). Independence is within each class; no "
                    + "coupling or independence between the two classes is required. Noise is added after the signal weight. The delays, noise laws and "
                    + "measures stay fixed when weights and classifiers are optimized.")),
                Paragraph(Text(
                    "For H= sensor(epsilon,.), phi_false=0 and phi_true=2pi/3, the actual observation is Y_b^w(omega)(j)=w_j H(phi_b-t_j)+xi_b,j(omega), "
                    + "and P_b^w=(mu_b).map(Y_b^w) on O=J -> B. Every classifier below is an arbitrary deterministic measurable delta:O -> Bool. Define "
                    + "R(w,delta)=[(P_false^w).real({y | delta(y)=true})+(P_true^w).real({y | delta(y)=false})]/2. Thus the objective is the original "
                    + "half-sum of class error probabilities. In particular, the optimization does not restrict delta to scores or replace its domain by "
                    + "the flattened Euclidean space.")),
                Paragraph(Text(
                    "Use the preceding actual flattening A(y)=toLp 2 (p -> y(p.1)(p.2)), means m_b^w=A(j -> w_j H(phi_b-t_j)), separation "
                    + "D(w)=norm(m_true^w-m_false^w), energy E(w)=sum_j w_j^2, and physical infimum g=lowerGain(epsilon). The C08 identities give "
                    + "g=sqrt(2epsilon/(9+20epsilon))>0 and D(w)=sqrt(3E(w))g for every such w and t. Set c_w=(m_false^w+m_true^w)/2. If D(w)>0 put "
                    + "u_w=(D(w))^(-1)(m_true^w-m_false^w), and let delta_w(y)=true exactly when inner(u_w,A(y)-c_w)>=0. If D(w)=0 let delta_w be constant "
                    + "false. The earlier C05/C06 argument gives Measurable(delta_w) and, for every measurable original delta, "
                    + "R(w,delta_w)=Phi(-sqrt(3E(w))g/(2sigma))<=R(w,delta), where Phi(x)=cdf(gaussianReal(0,1),x). The zero-separation branch uses equal "
                    + "laws, not division by D(w).")))),
            new DocumentBlock.Section(H("C09: the literal Gaussian quantile and the C10 energy cut"), Blocks(
                Paragraph(Text(
                    "Write Phi(x)=cdf(gaussianReal(0,1),x). This actual standard Gaussian CDF is continuous and strictly increasing on all real "
                    + "numbers, tends to zero at minus infinity and to one at plus infinity, satisfies Phi(-x)=1-Phi(x) for every real x and "
                    + "Phi(0)=1/2, and obeys 0<Phi(x)<1 at every finite real x. For each 0<p<1 define q(p)=sInf {x:R | p<=Phi(x)}, using the "
                    + "literal real infimum. No convention for q(0) or q(1) is needed.")),
                Paragraph(Text(
                    "The two limits bracket every interior p, so continuity and the intermediate value theorem give a real root r with "
                    + "Phi(r)=p. Strict monotonicity identifies {x:R | p<=Phi(x)} with Ici(r), whose infimum is r. Hence Phi(q(p))=p, this root "
                    + "is unique among all real numbers, and the same superlevel set is exactly Ici(q(p)). For every real x, Phi(x)=p iff "
                    + "x=q(p). Comparing with Phi(0)=1/2 gives all three signs: q(p)>0 iff p>1/2, q(p)=0 iff p=1/2, and q(p)<0 iff p<1/2. "
                    + "Together these facts identify the range of Phi as exactly (0,1). This is the literal-infimum application of "
                    + "stdNormalCDF_probit and stdNormalCDF_strictMono from the upstream source cited below.")),
                Paragraph(Text(
                    "For every 0<alpha<1/2 put q=q(1-alpha)=sInf {x:R | 1-alpha<=Phi(x)} and E_req=4sigma^2 q^2/(3g^2). Then q>0, "
                    + "Phi(q)=1-alpha and, by stdNormalCDF_neg, Phi(-q)=alpha. The value q is the unique positive real root of "
                    + "Phi(x)=1-alpha; indeed it is the unique real root, and {x:R | 1-alpha<=Phi(x)}=Ici(q). For every real s, including "
                    + "zero and negative s, strict monotonicity gives Phi(-s)<=alpha iff q<=s, and Phi(-s)=alpha iff s=q. These all-real "
                    + "comparisons are established before any squaring.")),
                Paragraph(Text(
                    "For E>=0 put s=sqrt(3E)g/(2sigma). Both s>=0 and q>0 are known, and 3g^2 and 4sigma^2 are positive. Therefore q<=s iff q^2<=s^2, "
                    + "while s=q iff s^2=q^2. Since s^2(4sigma^2)=3E g^2, multiplication and division by these positive factors yield "
                    + "Phi(-sqrt(3E)g/(2sigma))<=alpha iff E_req<=E, and equality to alpha iff E=E_req. The same signs show E_req>0. No positive-energy "
                    + "premise was introduced, so this calculation includes E=0.")),
                Paragraph(Text(
                    "Apply this cut to E=E(w). For every signed design w, R(w,delta_w)<=alpha iff E(w)>=E_req iff there exists a measurable deterministic "
                    + "delta:O -> Bool with R(w,delta)<=alpha. The forward existence direction uses this very delta_w. Conversely, any such delta satisfies "
                    + "R(w,delta_w)<=R(w,delta)<=alpha by the original all-classifier lower bound, so E(w)>=E_req. Moreover R(w,delta_w)=alpha iff "
                    + "E(w)=E_req. The equality assertion concerns the optimum midpoint risk; a nonoptimal classifier at a larger energy is not asserted to "
                    + "have a different risk. When J is empty, E(w)=D(w)=0 and every measurable original classifier has risk 1/2>alpha. Accordingly all "
                    + "three C10 threshold conditions are false, and neither energy equality to E_req nor midpoint risk equality to alpha occurs.")))),
            new DocumentBlock.Section(H("C11: the literal joint risk infimum and its same-design witness"), Blocks(
                Paragraph(Text(
                    "For a real budget E0>=0 define S(E0)={r:R | there exist w:J -> R and delta:O -> Bool such that E(w)<=E0, Measurable(delta), and "
                    + "R(w,delta)=r}, and C(E0)=sInf S(E0). This is one joint feasible set of the actual risk. Define the comparison curve "
                    + "F(E)=Phi(-sqrt(3E)g/(2sigma)) for E>=0. If 0<=E<=E0, monotonicity of the nonnegative square root, g>0, sigma>0 and monotonicity of "
                    + "Phi give F(E0)<=F(E). Thus every feasible pair satisfies F(E0)<=F(E(w))=R(w,delta_w)<=R(w,delta). The zero design with its "
                    + "constant-false midpoint is feasible and has risk 1/2, so S(E0) is nonempty; the displayed bound also makes it bounded below.")),
                Paragraph(Text(
                    "If J is nonempty, choose j0:J and set w^(E0)(j)=sqrt(E0) when j=j0 and zero otherwise. The finite sum and (sqrt(E0))^2=E0 give "
                    + "E(w^(E0))=E0, with all of the original fixed delays retained. Its own midpoint delta_(w^(E0)) is measurable and has actual risk "
                    + "F(E0). Hence F(E0) belongs to S(E0) and is no larger than any member. Applying IsLeast.csInf_eq to this attained least element gives "
                    + "C(E0)=Phi(-sqrt(3E0)g/(2sigma)). The witnesses are the single weight family and that family's actual midpoint together; the argument "
                    + "does not independently choose a weight optimum and an unrelated classifier optimum.")),
                Paragraph(Text(
                    "If J is empty, every weight has E(w)=0 and every measurable classifier has risk 1/2. Hence S(E0)={1/2} for every E0>=0, and "
                    + "C(E0)=1/2 is attained by the zero weight and its constant-false midpoint. Combining the cases gives C(E0)=if Nonempty J then "
                    + "Phi(-sqrt(3E0)g/(2sigma)) else 1/2. In both cases there exists one w with E(w)<=E0 and a measurable delta_w such that "
                    + "R(w,delta_w)=C(E0) and R(w,delta_w)<=R(v,delta) for every v,delta satisfying E(v)<=E0 and Measurable(delta).")))),
            new DocumentBlock.Section(H("Budget endpoints, saturation and the least feasible real budget"), Blocks(
                Paragraph(Text(
                    "There exists a weight family with E(w)=E0 if and only if J is nonempty or E0=0. For nonempty J use the single-index construction; "
                    + "for E0=0 use zero weights. Conversely, for empty J every finite energy sum is zero, so saturation forces E0=0. At zero budget "
                    + "C(0)=Phi(0)=1/2 in the nonempty case and C(0)=1/2 in the empty case. For an empty J and E0>0, the positive signs give "
                    + "sqrt(3E0)g/(2sigma)>0, so F(E0)<Phi(0)=1/2. That comparison value is unattainable by any feasible weight/classifier pair; the actual "
                    + "cap remains 1/2 even at positive budget.")),
                Paragraph(Text(
                    "For nonempty J, C(E0)<=alpha iff E_req<=E0. At E0=E_req choose j0:J, put w_req(j)=sqrt(E_req) when j=j0 and zero otherwise, and use "
                    + "its own delta_(w_req). This same pair satisfies E(w_req)=E_req, Measurable(delta_(w_req)), R(w_req,delta_(w_req))=alpha and "
                    + "C(E_req)=alpha. In particular, E_req belongs to the actual feasible-budget set B_alpha={B:R | 0<=B and there exist w,delta with "
                    + "E(w)<=B, Measurable(delta) and R(w,delta)<=alpha}. For any member B, its witnesses obey E_req<=E(w)<=B by C10. Thus E_req is the "
                    + "attained least element of B_alpha, not just a lower bound on budgets. For empty J this feasible-budget set is empty: no finite "
                    + "nonnegative B, design and original measurable classifier can achieve risk at most alpha.")))),
            new DocumentBlock.Section(H("The literal ENNReal energy minimum, including the empty feasible set"), Blocks(
                Paragraph(Text(
                    "Keep the same original experiment and classifier domain, and define T_alpha={z:ENNReal | there exist w:J -> R and delta:O -> Bool "
                    + "such that Measurable(delta), R(w,delta)<=alpha, and z=ENNReal.ofReal(E(w))}. Define M_alpha=sInf T_alpha in ENNReal. This definition "
                    + "optimizes the actual attained design energies, with each energy tied to its own feasible classifier. It is separate from the real "
                    + "risk infimum C(E0) and from the real feasible-budget set B_alpha.")),
                Paragraph(Text(
                    "For nonempty J use the single-index w_req and its own midpoint from the preceding paragraph. Since their actual risk is exactly "
                    + "alpha, z_req=ENNReal.ofReal(E_req)=ENNReal.ofReal(E(w_req)) belongs to T_alpha. Every z in T_alpha comes with a particular feasible "
                    + "w and delta, so C10 gives E_req<=E(w); ENNReal.ofReal_mono gives z_req<=ENNReal.ofReal(E(w))=z. Consequently z_req is an attained "
                    + "least element of this very set. The complete-order instance of IsLeast.csInf_eq yields M_alpha=ENNReal.ofReal(E_req), and the same "
                    + "pair w_req,delta_(w_req) attains it with real risk alpha.")),
                Paragraph(Text(
                    "For empty J every candidate measurable delta has R(w,delta)=1/2>alpha. Thus T_alpha is proved equal to the empty set. Unfolding the "
                    + "actual minimum and applying sInf_empty in ENNReal gives M_alpha=top, that is, infinity. No real empty-infimum convention is used for "
                    + "this conclusion. Altogether M_alpha=if Nonempty J then ENNReal.ofReal(E_req) else top, with the explicit joint attainment in the "
                    + "nonempty branch and the absence of every finite nonnegative feasible budget in the empty branch.")))),
            new DocumentBlock.Section(H("Supplier correspondence, external CDF provenance and applicability"), Blocks(
                Paragraph(Text(
                    "The geometry suppliers are the same sensor, physical lowerGain, six_chord_norm_sq, lower_gain_eq_sqrt and lower_gain_sq used in C08 "
                    + "above; the probability and all-classifier suppliers are those used in C01-C06 above. In the energy cut, the generic real variable E "
                    + "is E(w), the nonnegative score magnitude s is sqrt(3E(w))g/(2sigma), and the quantile probability is 1-alpha. In the cap argument, "
                    + "IsLeast.csInf_eq is applied to S(E0) with the actual risk of (w^(E0),delta_(w^(E0))); in the extended-energy argument it is applied "
                    + "to T_alpha with ENNReal.ofReal(E(w_req)). Mathlib at db584cd6d46c92f209a44c0f1c829460d327499d supplies the real square-order and "
                    + "nonnegative square-root identities, finite single-index sums, IsLeast.csInf_eq, ENNReal.ofReal_mono and sInf_empty. Each use has the "
                    + "positivity, membership and lower-bound premises supplied above.")),
                Paragraph(Text(
                    "The standard Gaussian CDF and probit facts used for the literal q are existing upstream mathematics from Jiyuan-Tan/CausalSmith, "
                    + "revision a7085d88d2e4b30003db7097ca374f4718da0f01, source Causalean/Mathlib/Probability/StdNormalCDF.lean. That source defines "
                    + "stdNormalCDF using cdf(gaussianReal 0 1) and probit through the same real sInf; its stdNormalCDF_probit and CDF continuity, "
                    + "strict-order and reflection results supply the quantile step at probability 1-alpha. The source is distributed under Apache-2.0 with "
                    + "its upstream NOTICE and provenance chain; the exact source and license are available at "
                    + "https://github.com/Jiyuan-Tan/CausalSmith/blob/a7085d88d2e4b30003db7097ca374f4718da0f01/Causalean/Mathlib/Probability/StdNormalCDF.lean "
                    + "and the LICENSE and NOTICE alongside the Causalean tree. This citation identifies an upstream mathematical result used in the "
                    + "application; it does not add a canonical Lean dependency. Canonical admission A17 remains open.")),
                Paragraph(Text(
                    "These C10/C11 conclusions apply to the finite original Gaussian experiment with fixed arbitrary delays, signed weights, equal class "
                    + "priors, isotropic positive post-weight noise and the stated epsilon and alpha ranges. The explicit witness presumes freedom to "
                    + "choose a real weight at one existing index; it makes no claim about hardware amplitude constraints, delay optimization, non-Gaussian "
                    + "or correlated noise, unequal priors, or physical implementation costs beyond E=sum_j w_j^2. This owning application introduces no "
                    + "new Lean mathematical declaration or library novelty. C07, canonical C09/A17 and C12/C13 remain outside this application, and it "
                    + "does not complete the parent problem.")))),
            new DocumentBlock.Section(H("C12/C13: varying budgets at the physical rank-defect scale"), Blocks(
                Paragraph(Text(
                    "The following extension keeps the full C10/C11 experiment and changes only the budget as epsilon tends to zero through positive values. Fix an "
                    + "arbitrary finite J, possibly empty, fixed delays t:J -> R and sigma>0. The measurable space Omega, probability measures mu_a for a in Bool, "
                    + "AEMeasurable noises xi_a,j, within-class independence and six-dimensional laws (mu_a).map(xi_a,j)=multivariateGaussian(0,sigma^2 I) are exactly "
                    + "those above and remain fixed. There is no cross-class coupling premise. For each epsilon and signed real weight family w, use the same "
                    + "post-weight-noise observation Y_a^w, its actual law P_a^w, the original domain O=J -> B, energy E(w)=sum_j w_j^2 and risk R_epsilon(w,delta) for "
                    + "every deterministic measurable delta:O -> Bool. Weights and classifiers are optimized jointly at each epsilon; no continuity or measurability of "
                    + "their choice as a function of epsilon is required.")),
                Paragraph(Text(
                    "Let b:R -> R be any budget function that is eventually nonnegative on nhdsWithin(0,Ioi(0)): there is a punctured positive neighborhood on which "
                    + "b(epsilon)>=0. No continuity, measurability, monotonicity, boundedness or strict positivity is assumed for b. It may vanish identically or at "
                    + "infinitely many positive parameters. Define g(epsilon)=lowerGain(epsilon), gap(epsilon)=2-actualRank(epsilon), and "
                    + "X(epsilon)=b(epsilon)gap(epsilon)^2, using the actual physical infima already defined. Write Cap_epsilon(B)=sInf {r:R | there exist w:J -> R and "
                    + "delta:O -> Bool with E(w)<=B, Measurable(delta) and R_epsilon(w,delta)=r}. Thus Cap_epsilon(b(epsilon)) is the literal joint actual-risk infimum "
                    + "C(B) above, now with epsilon displayed; it is not defined to be a comparison curve. Every eventual assertion below is with respect to "
                    + "nhdsWithin(0,Ioi(0)). Values of b away from its nonnegative tail play no role.")),
                Paragraph(Text(
                    "The existing geometry owner gives (2-actualRank(epsilon))/sqrt(epsilon/2)->1 by actual_rank_defect_scaled_limit and "
                    + "(2-actualRank(epsilon))/lowerGain(epsilon)->3/2 by actual_rank_defect_lower_gain_limit. Eventually 0<epsilon<=1/2, so lower_gain_eq_sqrt gives "
                    + "g(epsilon)=sqrt(2epsilon/(9+20epsilon))>0. The first normalized limit is eventually positive; since sqrt(epsilon/2)>0, gap(epsilon)>0 on a "
                    + "sufficiently small positive neighborhood. Multiplying that normalized limit by sqrt(epsilon/2)->0 proves gap(epsilon)->0. Inverting the second "
                    + "limit, whose value 3/2 is nonzero, proves g(epsilon)/gap(epsilon)->2/3. These are consequences of the physical rank and chord-gain definitions, "
                    + "with no substitute rank proxy.")))),
            new DocumentBlock.Section(H("C12 finite scale, including zero budgets and a zero limit"), Blocks(
                Paragraph(Text(
                    "Assume J is nonempty and X(epsilon)->L for a finite real L>=0. On the common tail where 0<epsilon<=1/2 and b(epsilon)>=0, C11 gives "
                    + "Cap_epsilon(b(epsilon))=Phi(-sqrt(3b(epsilon))g(epsilon)/(2sigma)). At each such parameter it is attained by the single-index weight "
                    + "sqrt(b(epsilon)) and that weight's own actual midpoint classifier, with the zero-separation constant-false branch when b(epsilon)=0. Thus the "
                    + "equality applies to the literal joint infimum under the original Gaussian law and all-classifier optimization.")),
                Paragraph(Text(
                    "The exact score rescaling on this tail is sqrt(3b(epsilon))g(epsilon)/(2sigma)=sqrt(3X(epsilon))(g(epsilon)/gap(epsilon))/(2sigma). Indeed "
                    + "sqrt(3(b gap^2))=sqrt(3b)gap when b>=0 and gap>0; only gap is cancelled. There is no division by b or sqrt(b), so zero budgets remain covered. "
                    + "Continuity of the nonnegative square root and the physical ratio limit give the score limit sqrt(3L)(2/3)/(2sigma)=sqrt(L/3)/sigma. Continuity of "
                    + "the actual standard Gaussian CDF then gives Cap_epsilon(b(epsilon))->Phi(-sqrt(L/3)/sigma).")),
                Paragraph(Text(
                    "When L=0 this limit is Phi(0)=1/2. When L>0, sqrt(L/3)/sigma>0, strict monotonicity gives Phi(-sqrt(L/3)/sigma)<Phi(0)=1/2, and the Gaussian CDF "
                    + "is strictly positive at every finite argument. Hence the limiting risk lies strictly between zero and one half. This finite-scale conclusion "
                    + "includes b identically zero and does not require eventual strict positivity of b.")))),
            new DocumentBlock.Section(H("C12 infinite scale and the separate empty-design boundary"), Blocks(
                Paragraph(Text(
                    "For nonempty J, if X tends to atTop, then sqrt(3X) tends to atTop, while (g/gap)/(2sigma) tends to 1/(3sigma)>0. Consequently the negative "
                    + "rescaled score tends to atBot. The standard Gaussian CDF tends to zero at atBot, and the same exact C11 cap equality gives "
                    + "Cap_epsilon(b(epsilon))->0. This statement uses divergence of X to positive infinity, not merely unboundedness along a subsequence.")),
                Paragraph(Text(
                    "For empty J, the conclusion is different for every eventually nonnegative b, with no restriction at all on X. Every weight family has E(w)=0, the "
                    + "two actual observation laws coincide, and every measurable classifier has risk 1/2. For each nonnegative budget the zero weight and "
                    + "constant-false classifier are feasible, so the literal risk set is {1/2}. Thus Cap_epsilon(b(epsilon)) is eventually exactly 1/2 and tends to "
                    + "1/2, even if X tends to atTop. For every real B>0 there is no w:J -> R with E(w)=B. A positive budget does not create an observation index or "
                    + "make positive energy attainable.")))),
            new DocumentBlock.Section(H("C13 exact least energy before taking a limit"), Blocks(
                Paragraph(Text(
                    "Fix also 0<alpha<1/2 and keep the literal quantile q=sInf {x:R | 1-alpha<=Phi(x)}, where Phi(x)=cdf(gaussianReal(0,1),x). The preceding CDF "
                    + "argument gives q>0, Phi(q)=1-alpha and Phi(-q)=alpha. For every 0<epsilon<=1/2 define E_req(epsilon)=4sigma^2 q^2/(3g(epsilon)^2)>0. Define the "
                    + "actual feasible-energy set T_epsilon,alpha={z:ENNReal | there exist w:J -> R and delta:O -> Bool with Measurable(delta), "
                    + "R_epsilon(w,delta)<=alpha and z=ENNReal.ofReal(E(w))}, and M_epsilon,alpha=sInf T_epsilon,alpha in ENNReal. These are exactly the original "
                    + "attained energies, each with its own classifier witness.")),
                Paragraph(Text(
                    "For nonempty J, choose j0:J and w_req(j)=sqrt(E_req(epsilon)) at j0 and zero elsewhere, retaining all fixed delays. Its own actual midpoint "
                    + "delta_req is measurable, E(w_req)=E_req(epsilon), and R_epsilon(w_req,delta_req)=alpha. For every z in T_epsilon,alpha, its witnesses satisfy "
                    + "E_req(epsilon)<=E(w) by the exact C10 cut. Monotonicity of ENNReal.ofReal makes ENNReal.ofReal(E_req(epsilon)) a lower bound on that same set, "
                    + "while the displayed pair proves membership. Thus IsLeast T_epsilon,alpha (ENNReal.ofReal(E_req(epsilon))) holds and "
                    + "M_epsilon,alpha=ENNReal.ofReal(E_req(epsilon)). The single pair w_req,delta_req simultaneously attains the energy minimum and equality to alpha; "
                    + "no unrelated witnesses are combined.")),
                Paragraph(Text(
                    "The same pair proves membership of E_req(epsilon) in B_epsilon,alpha={B:R | 0<=B and there exist w,delta with E(w)<=B, Measurable(delta) and "
                    + "R_epsilon(w,delta)<=alpha}. Every member obeys E_req(epsilon)<=E(w)<=B, so IsLeast B_epsilon,alpha E_req(epsilon) is the exact least-real-budget "
                    + "assertion. In particular, for nonempty J and B>=0, Cap_epsilon(B)<=alpha iff E_req(epsilon)<=B. If J is empty, every measurable classifier has "
                    + "risk 1/2>alpha; both feasible sets are empty and M_epsilon,alpha=top by the ENNReal empty-infimum law. The positive real formula E_req still "
                    + "exists but is not an attainable minimum in this empty-design case.")))),
            new DocumentBlock.Section(H("C13 asymptotic equivalence for the least real budget"), Blocks(
                Paragraph(Text(
                    "Put C_alpha=3sigma^2 q^2, which is strictly positive. On the positive tail, E_req(epsilon)gap(epsilon)^2=(4sigma^2 "
                    + "q^2/3)(gap(epsilon)/g(epsilon))^2. The physical ratio limit gap/g->3/2 therefore gives E_req(epsilon)gap(epsilon)^2->C_alpha. Moreover "
                    + "E_req(epsilon)/(C_alpha/gap(epsilon)^2)=E_req(epsilon)gap(epsilon)^2/C_alpha on that tail, where both C_alpha and gap are nonzero. This quotient "
                    + "tends to one. Applying Asymptotics.isEquivalent_of_tendsto_one yields the actual relation Asymptotics.IsEquivalent (nhdsWithin(0,Ioi(0))) "
                    + "(epsilon -> E_req(epsilon)) (epsilon -> C_alpha/gap(epsilon)^2).")),
                Paragraph(Text(
                    "The product limit and IsEquivalent statement concern the exact real E_req with the literal quantile and actual physical lower gain and rank "
                    + "defect. With nonempty J they describe the attained least real budget and, via ENNReal.ofReal, the exact finite extended minimum at each "
                    + "0<epsilon<=1/2. The formulas themselves have no nonempty-J premise, but when J is empty the actual extended minimum remains top. Equivalence is a "
                    + "limiting comparison and supplies no finite-epsilon feasibility conclusion at equality of leading scales.")))),
            new DocumentBlock.Section(H("C13 subcritical, critical and supercritical risk regimes"), Blocks(
                Paragraph(Text(
                    "Assume J is nonempty and retain an arbitrary eventually nonnegative b. For finite X->L>=0, the risk limit is H_sigma(L)=Phi(-sqrt(L/3)/sigma). "
                    + "Because C_alpha/3=(sigma q)^2 and sigma q>0, sqrt(C_alpha/3)/sigma=q, so H_sigma(C_alpha)=Phi(-q)=alpha. The square root is strictly increasing "
                    + "on nonnegative arguments, division by sigma preserves order, negation reverses it and Phi is strictly increasing. Hence L<C_alpha gives "
                    + "H_sigma(L)>alpha; convergence then gives Cap_epsilon(b(epsilon))>alpha eventually. No feasible weight/classifier pair can meet the target on that "
                    + "tail. Equivalently the exact cut gives b(epsilon)<E_req(epsilon) there.")),
                Paragraph(Text(
                    "If C_alpha<L<infinity, the limiting risk is strictly below alpha, so Cap_epsilon(b(epsilon))<alpha eventually. The actual same-design C11 "
                    + "minimizer then meets the target with strict slack. The exact cap curve equals alpha at E_req and is strictly decreasing for nonnegative budgets, "
                    + "so b(epsilon)>E_req(epsilon) on that tail. If X tends to atTop, C12 instead gives risk tending to zero, which is eventually strictly below any "
                    + "fixed alpha>0; the same attainment and budget comparison apply when 0<alpha<1/2. The atTop risk comparison itself needs only alpha>0, not a "
                    + "quantile or an upper bound on alpha.")),
                Paragraph(Text(
                    "At the critical scale L=C_alpha, the conclusion is only Cap_epsilon(b(epsilon))->alpha. Neither the product limit nor the IsEquivalent relation "
                    + "implies Cap_epsilon(b(epsilon))<=alpha at any specified positive epsilon, or even eventually. Exact finite-parameter feasibility still requires "
                    + "the exact comparison b(epsilon)>=E_req(epsilon).")))),
            new DocumentBlock.Section(H("An explicit critical-scale budget that always misses the target"), Blocks(
                Paragraph(Text(
                    "For nonempty J and 0<alpha<1/2 set b(epsilon)=(1-epsilon)E_req(epsilon). For EVERY 0<epsilon<=1/2, positivity of E_req and 1/2<=1-epsilon<1 gives "
                    + "0<=b(epsilon)<E_req(epsilon). The exact C11 threshold therefore gives Cap_epsilon(b(epsilon))>alpha for every parameter in this entire interval, "
                    + "not just eventually. This bound is on the literal joint risk infimum, so no signed weight design and measurable original classifier under this "
                    + "budget can attain risk at most alpha.")),
                Paragraph(Text(
                    "Nevertheless, (1-epsilon)->1 and E_req(epsilon)gap(epsilon)^2->C_alpha, so b(epsilon)gap(epsilon)^2->C_alpha. The critical finite-scale result "
                    + "gives Cap_epsilon(b(epsilon))->alpha. This explicit budget has the critical leading scale while remaining strictly infeasible at every "
                    + "0<epsilon<=1/2. It supplies the boundary case that prevents replacing the exact least-budget criterion by asymptotic equivalence.")))),
            new DocumentBlock.Section(H("C12/C13 supplier correspondence and applicability"), Blocks(
                Paragraph(Text(
                    "All geometry in this extension is supplied by D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry: actualRank, "
                    + "lowerGain, actual_rank_defect_scaled_limit, actual_rank_defect_lower_gain_limit and lower_gain_eq_sqrt. The joint cap equality, same-design "
                    + "attainment, literal ENNReal minimum and exact budget cut are the C10/C11 applications derived above from the actual observation laws and C01-C08 "
                    + "suppliers. In the finite-scale application the generic nonnegative energy is b(epsilon), the rescaled variable is X=b gap^2, and the score is "
                    + "sqrt(3X)(g/gap)/(2sigma). In the least-energy application the comparison constant is C_alpha=3sigma^2 q^2. Every division and square-root step "
                    + "uses the signs established above, without imposing new regularity on b.")),
                Paragraph(Text(
                    "Mathlib at db584cd6d46c92f209a44c0f1c829460d327499d supplies the filter limit algebra, Tendsto.inv₀, nonnegative "
                    + "square-root continuity and strict order, Real.tendsto_sqrt_atTop, ProbabilityTheory.tendsto_cdf_atBot, eventual strict comparison of convergent "
                    + "functions, and Asymptotics.isEquivalent_of_tendsto_one. The CDF continuity, strict-order, reflection and literal-probit correspondence remain the "
                    + "existing C09 supplier from Jiyuan-Tan/CausalSmith at a7085d88d2e4b30003db7097ca374f4718da0f01, Causalean/Mathlib/Probability/StdNormalCDF.lean, "
                    + "under Apache-2.0 with its NOTICE and provenance as cited above. Canonical admission A17 remains open; this exposition introduces no canonical "
                    + "dependency on that external source.")),
                Paragraph(Text(
                    "The conclusions concern the original finite equal-prior Gaussian experiment with fixed delays, arbitrary signed signal weights, isotropic "
                    + "positive noise added after weighting and arbitrary measurable deterministic classifiers. They retain empty designs, zero budgets and the critical "
                    + "boundary. They do not address amplitude-constrained hardware, delay optimization, correlated or non-Gaussian noise, unequal priors or costs "
                    + "beyond sum_j w_j^2. The eight conclusions here are applications of existing mathematics, with zero new Lean mathematical declarations, Describe "
                    + "blocks or library-novelty credit. C07 and canonical C09/A17 remain outside this extension; no completion of the parent problem is asserted.")))),
            new DocumentBlock.Section(H("C07: two arbitrary equal-energy Gaussian designs"), Blocks(
                Paragraph(Text(
                    "Fix the same 0<epsilon<=1/2 and sigma>0 for two designs indexed by arbitrary finite types J and K, either of which "
                    + "may be empty. In this section K denotes the second design's index type; the six sensor coordinates remain Fin 3 x "
                    + "Fin 2 and B=EuclideanSpace R (Fin 3 x Fin 2). Choose arbitrary signed weights wJ:J -> R and wK:K -> R and arbitrary "
                    + "known delays tJ:J -> R and tK:K -> R. Assume equality of the actual energies EJ=sum_j wJ(j)^2 and EK=sum_k wK(k)^2, "
                    + "and write E=EJ=EK. There is no requirement that J and K have the same cardinality or that their weights, delays or "
                    + "observation spaces coincide.")),
                Paragraph(Text(
                    "For each I=J,K separately, take a measurable sample space Omega_I, probability measures mu_I,b for b in Bool, and "
                    + "AE-measurable noises xi_I,b,i:Omega_I -> B. Under each mu_I,b assume that the entire family (xi_I,b,i)_i is "
                    + "independent and every member has law multivariateGaussian(0,sigma^2 I_(Fin 3 x Fin 2)). Put phi_false=0, "
                    + "phi_true=2pi/3, s_I,b(i)=wI(i) sensor(epsilon,phi_b-tI(i)), Y_I,b(omega)(i)=s_I,b(i)+xi_I,b,i(omega), and "
                    + "P_I,b=(mu_I,b).map(Y_I,b) on O_I=I -> B. These are separate full Gaussian-noise assumptions for each actual "
                    + "experiment and label. No coupling or independence between the two designs or between labels is required. Noise is "
                    + "added after weighting the signal and retains covariance sigma^2 I at zero as well as nonzero weights.")),
                Paragraph(Text(
                    "Use the actual flattening A_I:O_I -> V_I=EuclideanSpace R (I x (Fin 3 x Fin 2)), A_I(y)=toLp 2 (p -> y(p.1)(p.2)). "
                    + "Set m_I,b=A_I(s_I,b), d_I=m_I,true-m_I,false and D_I=norm(d_I). This is the coordinate convention already "
                    + "identified with the Fin 6 version above. Apply the original observation-law argument independently for I=J and I=K: "
                    + "P_I,b.map(A_I)=multivariateGaussian(m_I,b,sigma^2 I), and pushing this law back through A_I^{-1} recovers P_I,b. In "
                    + "particular, neither design's noise law or classifier is substituted into the other design.")))),
            new DocumentBlock.Section(H("The two literal risk infima and their own attaining rules"), Blocks(
                Paragraph(Text(
                    "For every measurable deterministic delta:O_I -> Bool define R_I(delta)=[P_I,false.real({y | "
                    + "delta(y)=true})+P_I,true.real({y | delta(y)=false})]/2. Define pInf_I=sInf {r:R | there exists delta:O_I -> Bool "
                    + "with Measurable(delta) and R_I(delta)=r}, using the real sInf of all actual measurable deterministic classifier "
                    + "risks. Each event probability is taken under that design's original law. The optimization has no threshold-only "
                    + "restriction, finite candidate list or additional bound on classifiers.")),
                Paragraph(Text(
                    "For D_I>0 put u_I=D_I^{-1} d_I, c_I=(m_I,false+m_I,true)/2 and T_I(x)=inner(u_I,x-c_I). Define deltaStar_I(y)=true "
                    + "exactly when 0<=T_I(A_I(y)), with true at a midpoint tie. For D_I=0 define deltaStar_I to be the constant-false "
                    + "rule. For EACH I=J,K this is a measurable deterministic rule on O_I, and R_I(deltaStar_I)=pInf_I<=R_I(delta) for "
                    + "every measurable delta:O_I -> Bool. Thus each design attains its own literal infimum with its own actual midpoint "
                    + "classifier, including the constant-false coincident-mean convention.")))),
            new DocumentBlock.Section(H("Equal actual energy gives exactly equal optimized risk"), Blocks(
                Paragraph(Text(
                    "Let Phi(x)=cdf(gaussianReal(0,1),x). The common value is pInf_J=pInf_K=Phi(-(sqrt(3E) "
                    + "lowerGain(epsilon))/(2sigma))=Phi(-sqrt(6epsilon E/(9+20epsilon))/(2sigma)). Both displayed formulas hold "
                    + "separately for each infimum and, by attainment, for R_J(deltaStar_J) and R_K(deltaStar_K). The lowerGain is the "
                    + "actual physical chord-gain infimum defined above.")),
                Paragraph(Text(
                    "To derive the formulas, first apply the C05/C06 all-classifier argument separately to each actual law. Its Fubini "
                    + "reduction and pointwise Gaussian-density domination bound EVERY original measurable rule below by "
                    + "Phi(-D_I/(2sigma)); its actual midpoint rule attains that bound. The attainable risk set is nonempty and bounded "
                    + "below, and the attained least-element identity IsLeast.csInf_eq therefore gives pInf_I=Phi(-D_I/(2sigma)). This "
                    + "risk identity is a conclusion of the stated full noise model, not an extra premise about either experiment.")),
                Paragraph(Text(
                    "Next apply the C08 geometric identities separately to the same signed means: D_I^2=6epsilon E_I/(9+20epsilon) and "
                    + "D_I=sqrt(3E_I) lowerGain(epsilon)=sqrt(6epsilon E_I/(9+20epsilon)). The delayed third-turn chord square is "
                    + "6epsilon/(9+20epsilon), independently of the delay; Euclidean block squares add and the signed weight contributes "
                    + "wI(i)^2. Since E_I>=0, D_I>=0 and lowerGain(epsilon)>0, these are the nonnegative square-root branches, including "
                    + "E_I=0. Substitution into each independently obtained risk formula gives its energy expression. Only then use EJ=EK "
                    + "to equate the two scalar values. This does not compare vectors in different dimensions or combine a mean, noise law "
                    + "or witness from different designs.")))),
            new DocumentBlock.Section(H("Zero energy, either empty index type and scope of the comparison"), Blocks(
                Paragraph(Text(
                    "If E=0, both D_J and D_K vanish. Within EACH experiment P_I,true=P_I,false, and the two Boolean error events are "
                    + "measurable complements under that common probability law. Hence every measurable classifier on O_I has "
                    + "R_I(delta)=1/2. Both literal infima and both constant-false attaining risks are 1/2, consistently with Phi(0)=1/2. "
                    + "This includes all-zero weights on nonempty index types; equality here is between the two labels within an "
                    + "experiment, without asserting equality of measures on O_J and O_K.")),
                Paragraph(Text(
                    "If J is empty, EJ=0, and the energy-equality assumption also forces EK=0; consequently both infima are 1/2. If K is "
                    + "empty, EK=0 and EJ=0 give the same conclusion. The other index type need not be empty. These statements use the "
                    + "actual empty finite sum and the preceding coincident-law argument. Setting K=J is an internal specialization of "
                    + "this arbitrary-two-type comparison and adds no assumption or separate result.")),
                Paragraph(Text(
                    "The supplier correspondence is the C05/C06 actual-law risk argument with I, Omega_I, wI, tI, mu_I and xi_I "
                    + "substituted separately for each experiment, followed by the C08 energy identities with exactly those same epsilon, "
                    + "wI and tI. The geometric suppliers are sensor, six_chord_norm_sq, lower_gain_sq and lower_gain_eq_sqrt in "
                    + "SixDimensionalSharpGeometry; the probability, finite-product, Gaussian and real-infimum suppliers are the existing "
                    + "Mathlib results identified above at db584cd6d46c92f209a44c0f1c829460d327499d. The final step is substitution of the "
                    + "assumed equality of finite sums of squared weights. The comparison concerns equal priors, the fixed two phases, the "
                    + "common epsilon and positive post-weight isotropic noise scale, arbitrary known delays and all measurable "
                    + "deterministic classifiers. It does not extend the equality to unequal noise scales, correlated or non-Gaussian "
                    + "noise, unequal priors or a different pair of phases.")))))));

    private static Formula ActualEtaLimitFormula() => Disp(Call("Tendsto",
        Seq(Open, Varepsilon, Colon, Sp, Mathbb, Grp(F.Id("R")), Close,
            Sp, Mapsto, Sp, Frac, Grp(Call("actualEta", Varepsilon)),
            Grp(Sqrt, Grp(Varepsilon))),
        Call("nhdsWithin", Num(0), Call("Ioi", Num(0))),
        Call("nhds", Seq(Frac, Grp(Num(1)),
            Grp(Num(2), Sp, Cdot, Sp, Sqrt, Grp(Num(2)))))));

    private static Formula RankDefectGainLimitFormula() => Disp(Call("Tendsto",
        Seq(Open, Varepsilon, Colon, Sp, Mathbb, Grp(F.Id("R")), Close,
            Sp, Mapsto, Sp, Frac,
            Grp(Num(2), Sp, Minus, Sp, Call("actualRank", Varepsilon)),
            Grp(Call("lowerGain", Varepsilon))),
        Call("nhdsWithin", Num(0), Call("Ioi", Num(0))),
        Call("nhds", Seq(Frac, Grp(Num(3)), Grp(Num(2))))));

}
