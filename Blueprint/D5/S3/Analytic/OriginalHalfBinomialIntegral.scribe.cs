using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized central-binomial series give the elliptic sine integral and the closed-interval arcsine expansion.",
        H("Original Half-Binomial Integrals and the Arcsine Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-half-binomial-normalized-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b"),
                H("The normalized central-binomial coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Call("b", F.Id("n")), Eq,
                    Frac, Grp(Call("centralBinom", F.Id("n"))),
                    Grp(D(4), Caret, Grp(F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, b(n) is the real central-binomial "
                    + "coefficient divided by 4^n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-multichoose"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_multichoose"),
                H("The half-parameter multichoose coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, Ring.multichoose (1/2 : Real) n "
                    + "equals b(n). This coefficient identity supplies the binomial power-series "
                    + "step in the integral representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-coefficient-nonnegative"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_nonneg"),
                H("Nonnegativity of every normalized coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, 0<=b(n). The central-binomial "
                    + "coefficient is nonnegative and its denominator 4^n is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-coefficient-upper-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.b_le_one"),
                H("A uniform upper bound for the normalized coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, b(n)<=1. The central-binomial "
                    + "bound centralBinom(n)<=4^n gives this estimate, including n=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-half-binomial-kernel-series"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.binomial_hasSum"),
                H("The square-root kernel as a binomial series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real u with 0<=u<1, the series with nth "
                    + "term b(n)u^n has sum 1/sqrt(1-u). The parameter is the argument of "
                    + "the binomial series; in the arcsine integral it is t^2, whereas in "
                    + "the elliptic sine integral it is r*sin(theta)^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("original-half-binomial-elliptic-integral"),
            DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.original_series_eq_integral"),
            H("Summability, integrability and the exact identity including zero"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every real r with 0<=r<1, the complex series with nth term "
                    + "halfBinomial(n)^2 times (r:Complex)^n is summable. The real function "
                    + "theta maps to 1/sqrt(1-r*sin(theta)^2) is interval integrable from zero "
                    + "to pi/2, and the sum of that same complex series equals the complex "
                    + "embedding of (2/pi) times that real integral. The original coefficient "
                    + "halfBinomial(n) is the product of (-1/2-j) for 0<=j<n, divided by n!, "
                    + "including its zeroth term and its alternating sign before squaring. No analytic identity or "
                    + "convergence assertion is a hypothesis.")),
                Paragraph(Text("Write b_n=centralBinom(n)/4^n. The original successor law gives "
                    + "halfBinomial(n)=(-1)^n b_n. Mathlib's binomial power series identifies "
                    + "sum b_n u^n with 1/sqrt(1-u) for 0<=u<1. The sine-power reduction "
                    + "formula gives integral from zero to pi/2 of sin(theta)^(2n) equal "
                    + "to (pi/2)b_n. Each term b_n r^n sin(theta)^(2n) is bounded in "
                    + "absolute value by r^n, since 0<=b_n<=1 and sin(theta)^2<=1. "
                    + "The summable geometric bound justifies termwise interval integration. "
                    + "Continuity and the lower bound 1-r>0 give actual integrability of "
                    + "the square-root kernel. Uniqueness of sums and the real-to-complex "
                    + "continuous embedding yield the displayed literal identity.")),
                Paragraph(Text("This is the classical Euler-Gauss representation of the "
                    + "complete elliptic integral, with parameter r and normalization 2/pi. "
                    + "No originality claim is made. The result supplies the analytic bridge "
                    + "needed for complementary-period endpoint estimates; it does not "
                    + "establish the logarithmic constant, the nome, an original Gaussian "
                    + "realization, crossing, string theory or an AdS/CFT correspondence."))),
            DescribeRole.Theorem),
            new DocumentBlock.Section(H("An arcsine application on the closed interval"), Blocks(
            Paragraph(Text("For every natural n define the rational coefficient "
                + "c_n=choose(2n,n)/(4^n(2n+1)), and let a_n be its image in the reals. "
                + "Since centralBinom(n)=choose(2n,n), a_n=b(n)/(2n+1). Thus "
                + "0<=a_n<=1. For every real x with |x|<=1 the series with nth term "
                + "a_n*x^(2n+1) has sum arcsin(x). Both x=1 and x=-1 are included; "
                + "their sums are pi/2 and -pi/2, respectively.")),
            Paragraph(Text("To obtain the endpoint as well as the interior, fix 0<=y<=1 "
                + "and put K(t)=1/sqrt(1-t^2). The function arcsin is continuous on [0,y], "
                + "and for 0<t<y its derivative is K(t)>=0. The interval-integrability "
                + "theorem for a nonnegative derivative therefore makes K integrable "
                + "on 0..y, including y=1. The fundamental theorem of calculus and "
                + "arcsin(0)=0 give the integral of K on 0..y equal to arcsin(y). "
                + "Neither theorem requests a derivative at the upper endpoint.")),
            Paragraph(Text("Set F_n(t)=b(n)*t^(2n) and H(t)=sum_n F_n(t), where H is "
                + "the total infinite-sum function. On 0<t<y the substitution u=t^2 "
                + "satisfies 0<=u<1, so binomial_hasSum identifies the sum with K(t). "
                + "Equality on this open interval transfers interval integrability "
                + "from K to H. Each F_n is continuous and nonnegative, hence "
                + "measurable with |F_n(t)|=F_n(t). Use F_n itself as the nth bound "
                + "in the series dominated-convergence theorem. The bounds are "
                + "summable almost everywhere on (0,y], their total H is integrable, "
                + "and the same binomial series gives the required sum K almost "
                + "everywhere. The only excluded upper endpoint is a null singleton. "
                + "This verifies every premise of termwise integration without "
                + "assuming a binomial-series value at t=1.")),
            Paragraph(Text("Termwise integration gives the nth integral "
                + "b(n)*y^(2n+1)/(2n+1)=a_n*y^(2n+1). Its total is the integral "
                + "of K, hence arcsin(y). This also handles y=0, where the open "
                + "interval is empty and every integrated term is zero. For x<0, "
                + "apply the nonnegative result to -x, negate its HasSum, and use "
                + "arcsin(-x)=-arcsin(x) and the odd exponents. This yields the "
                + "same series on the whole closed interval [-1,1].")))),
            new DocumentBlock.Section(H("Interior truncation and the function A"), Blocks(
            Paragraph(Text("For all real x,q and natural N satisfying 0<=q<1 and "
                + "|x|<=q, write S_N(x)=sum_{0<=n<N} a_n*x^(2n+1). Coefficient "
                + "nonnegativity and a_n<=1 give |a_n*x^(2n+1)|<=q*(q^2)^n. "
                + "The geometric-series remainder theorem with C=q and r=q^2 "
                + "therefore gives |arcsin(x)-S_N(x)|<=q^(2N+1)/(1-q^2). "
                + "The denominator is positive, and the power identity "
                + "q*(q^2)^N=q^(2N+1) uses no division by q. Consequently the "
                + "bound includes q=0 and N=0.")),
            Paragraph(Text("Define A(x)=2*x+2*arcsin(x) and "
                + "A_N(x)=2*x+2*S_N(x). For every |x|<=1, A(x) equals "
                + "2*x+2*sum_n a_n*x^(2n+1). Under the interior assumptions "
                + "0<=q<1 and |x|<=q, cancellation of the 2*x terms gives "
                + "|A(x)-A_N(x)|<=2*q^(2N+1)/(1-q^2). These are classical "
                + "arcsine-series consequences of the normalized binomial kernel. "
                + "The endpoint convergence assertion supplies no endpoint "
                + "truncation rate; the displayed error bounds require q<1.")))),
            new DocumentBlock.Section(H("A conditional application to actual regular-action corners"), Blocks(
            new DocumentBlock.Section(H("Scalar kernel and associative Taylor correction"), Blocks(
            Paragraph(Text("For every integer n>=0, put b_n=centralBinom(n)/4^n. The declarations "
                + "b_nonneg, b_le_one and b_multichoose give 0<=b_n<=1 and "
                + "choose(-1/2,n)=(-1)^n b_n. The declaration binomial_hasSum gives "
                + "sum_{n>=0} b_n u^n=1/sqrt(1-u) for every real 0<=u<1. "
                + "These same normalized coefficients control an operator Taylor series.")),
            Paragraph(Text("Let A be any complete real normed associative algebra with identity I "
                + "of norm one. For every d in A with ||d||<1 define "
                + "S(d)=sum_{n>=0} choose(-1/2,n) d^n. Comparison with the scalar binomial "
                + "series proves absolute convergence. For every T in A with "
                + "||T^2-I||<1, set d_T=T^2-I and C_T=(I+T S(d_T))/2. "
                + "The Cauchy product and Chu-Vandermonde identity give "
                + "S(d_T)^2=sum_{n>=0} (-d_T)^n. Multiplication by I+d_T=T^2 "
                + "gives T^2 S(d_T)^2=I. Since T commutes with d_T and its convergent "
                + "power series, (T S(d_T))^2=I and C_T^2=C_T.")),
            Paragraph(Text("For every ||d||<1, the scalar majorant gives "
                + "||S(d)-I||<=1/sqrt(1-||d||)-1. If ||d||<=1/2 this is at most ||d||; "
                + "squaring the nonnegative quantities in "
                + "1<=(1+||d||)sqrt(1-||d||) verifies the last inequality. Thus "
                + "||C_T-(I+T)/2||<=(1/2)||T|| ||S(d_T)-I||. "
                + "If E,F are complete nontrivial complex normed spaces, s:E->F is "
                + "continuous and real linear, T and U are continuous complex-linear "
                + "endomorphisms, s(Tx)=U(sx) for every x, and both square defects have "
                + "norm less than one, then termwise transport of the real-coefficient "
                + "series gives s(C_T x)=C_U(sx). This includes conjugate-linear star.")))),
            new DocumentBlock.Section(H("Original product data and both norms"), Blocks(
            Paragraph(Text("Let H be any finite-dimensional complex Hilbert space with its "
                + "original additive conjugate-linear involution star, and let "
                + "mu:H x H->H be continuous and complex bilinear. Assume a strict "
                + "two-sided unit e with ||e||=1, star(mu(x,y))=mu(star y,star x), "
                + "and adjoint(L_x)=L_(star x), where L_x(z)=mu(x,z). "
                + "For real M>=1 and delta>=0 assume ||mu||_bil<=M and, for all x,y,z, "
                + "||mu(mu(x,y),z)-mu(x,mu(y,z))||<=delta ||x|| ||y|| ||z||. "
                + "All unqualified vector norms and adjoints here refer to this original "
                + "Hilbert structure.")),
            Paragraph(Text("For every x put p(x)=||L_x||_op. Evaluation at the actual unit "
                + "and the bilinear bound give ||x||<=p(x)<=M||x||. Also p(e)=1 and "
                + "p(star x)=p(x), the latter by the adjoint identity. The map "
                + "J:x->L_x is injective since L_x e=x. Its range, with the inherited "
                + "Hilbert-operator norm, is a complete complex normed space, and "
                + "||Jx||=p(x). Transport actual left and right multiplication through "
                + "J, writing ell_x=J L_x J^(-1) and rho_y=J R_y J^(-1), where "
                + "R_y(z)=mu(z,y). The associative algebra used for Taylor correction "
                + "is the endomorphism algebra of this range. H itself receives no "
                + "associative Ring or C*-algebra instance.")),
            Paragraph(Text("For every x,y,z the original associator estimate gives "
                + "||L_(mu(x,y))-L_x L_y||_op<=delta ||x|| ||y||, hence "
                + "p(mu(x,y))<=(1+delta)p(x)p(y) and "
                + "p(mu(mu(x,y),z)-mu(x,mu(y,z)))<=M delta p(x)p(y)p(z). "
                + "The operator identity ||adjoint(L_x)L_x||=p(x)^2 and the same "
                + "action defect give (1-delta)p(x)^2<=p(mu(star x,x)) "
                + "<=(1+delta)p(x)^2. These comparisons preserve both original norms; "
                + "they do not identify p with the Hilbert norm.")))),
            new DocumentBlock.Section(H("Actual labels, defect and compression"), Blocks(
            Paragraph(Text("Fix real tau>=0 and put r=tau+M delta. Call a label A allowed "
                + "when star A=A and p(mu(A,A)-A)<=tau. For any allowed P,Q, assume "
                + "r<=1/1024. The self-adjoint action identity and the actual projection "
                + "defects give p(P),p(Q)<=2. The transported actions have norms "
                + "||ell_P||,||rho_Q||<=3, and their actual defects satisfy "
                + "||ell_P^2-ell_P||<=M delta p(P)^2+(1+delta)tau, "
                + "||rho_Q^2-rho_Q||<=M delta p(Q)^2+(1+delta)tau, and "
                + "||ell_P rho_Q-rho_Q ell_P||<=M delta p(P)p(Q). "
                + "In particular each defect is at most 4r.")),
            Paragraph(Text("Set T=ell_P rho_Q+rho_Q ell_P-I for these actual actions. "
                + "Then ||T||<=19. To bound its square defect, put a=ell_P, b=rho_Q, "
                + "s=ab and E=ba-ab. The identity s^2-s=aEb+(a^2-a)b^2+a(b^2-b) "
                + "gives ||s^2-s||<=84r. Since T=2s-I+E, "
                + "T^2-I=4(s^2-s)+(2s-I)E+E(2s-I)+E^2. "
                + "Using ||2s-I||<=19 gives ||T^2-I||<=512r<=1/2<1. "
                + "Apply the literal series S to this derived operator defect and set "
                + "C(P,Q)=J^(-1) C_T J on the original H. It is a continuous "
                + "complex-linear idempotent. Define S_PQ=range C(P,Q). The construction "
                + "uses mu throughout; an assumed scalar defect never replaces the "
                + "derived defect of the actual operators.")))),
            new DocumentBlock.Section(H("Closeness, star and complements"), Blocks(
            Paragraph(Text("For every allowed P,Q at the preceding radius and every x in H, "
                + "p(C(P,Q)x-mu(P,mu(x,Q)))<=4866r p(x) and "
                + "p(C(P,Q)x-mu(mu(P,x),Q))<=4866r p(x). Indeed the Taylor tail is "
                + "at most 512r, so the midpoint displacement is at most "
                + "(19/2)512r=4864r. Half the actual commutator contributes at most "
                + "2r for either bracketing. The corresponding original Hilbert "
                + "operator bounds are ||C(P,Q)-L_P R_Q||_op<=4866Mr and "
                + "||C(P,Q)-R_Q L_P||_op<=4866Mr, by ||x||<=p(x)<=M||x||.")),
            Paragraph(Text("For all such P,Q,x, star(C(P,Q)x)=C(Q,P)star x. "
                + "Star reversal exchanges the actual left and right actions, and "
                + "p(star x)=p(x) makes the transported star a bounded real-linear "
                + "intertwiner for the Taylor series. This identity asserts no "
                + "orthogonality or positivity of the compression. The strict unit "
                + "is star fixed; e-Q has exactly Q's projection defect. The actual "
                + "uncorrected bracketings for Q and e-Q add to the one for e. "
                + "Consequently, for every x, "
                + "p(C(P,Q)x+C(P,e-Q)x-C(P,e)x)<=14598r p(x), "
                + "by three applications of 4866r closeness. This estimate is not "
                + "an exact direct-sum decomposition of the corrected ranges.")))),
            new DocumentBlock.Section(H("Compatible support and actual square nondegeneracy"), Blocks(
            Paragraph(Text("For any allowed P,Q,R, the same tau and r<=1/1024, "
                + "and every x in S_PQ and y in S_QR, "
                + "p(C(P,R)mu(x,y)-mu(x,y))<=260000r p(x)p(y). "
                + "To see the support estimates, idempotence fixes x under C(P,Q); "
                + "closeness and the associator bound give "
                + "p(mu(P,x)-x)<=24354r p(x). The four contributions have "
                + "coefficients 4·4866,16,8,4866, summing to 24354. Star reversal "
                + "gives p(mu(y,R)-y)<=24354r p(y). At this radius "
                + "p(mu(a,b))<=2p(a)p(b).")),
            Paragraph(Text("Telescope from C(P,R)mu(x,y) through "
                + "mu(P,mu(mu(x,y),R)), mu(P,mu(x,mu(y,R))), "
                + "mu(P,mu(x,y)), mu(mu(P,x),y), and finally mu(x,y). "
                + "In units of r p(x)p(y), the five errors are bounded respectively "
                + "by 9732, 8, 8·24354, 2, and 2·24354. Their sum is "
                + "253282<=260000. The numerical constant is independent of M; "
                + "M remains explicitly in r=tau+M delta.")),
            Paragraph(Text("If additionally 520000rM^2<=1, then for every allowed P,Q "
                + "and every x in S_PQ, "
                + "(1/2)||x||^2<=Re<e,C(Q,Q)mu(star x,x)>, and "
                + "C(Q,Q)mu(star x,x)=0 if and only if x=0. The original adjoint "
                + "law and strict right unit give exactly "
                + "<e,mu(star x,x)>=<x,x>. Star covariance puts star x in S_QP; "
                + "compatible support bounds the compressed-square error by "
                + "260000r p(x)^2. Cauchy-Schwarz, ||e||=1 and p(x)<=M||x|| "
                + "give the half-norm lower bound. The loss M^2 is explicit. "
                + "Nondegeneracy alone selects no rank-one corner and proves no saturation.")))),
            new DocumentBlock.Section(H("Conditional rank-one line, coefficient and scale"), Blocks(
            Paragraph(Text("In addition to the original product data, allowed Q and both "
                + "radii r<=1/1024 and 520000rM^2<=1, assume exactly "
                + "dim_C(S_QQ)=1. Set t=C(Q,Q)Q, with this literal generator and "
                + "no rescaling. The estimates give p(t-Q)<=9737r, "
                + "p(C(Q,Q)Z)<=5p(Z) for every Z in H, and "
                + "p(C(Q,Q)mu(t,X)-X)<=219140r p(X) for every X in S_QQ. "
                + "Here 219140=5·(2·9737+24354), and the additional radius implies "
                + "219140r<1. If t were zero this action estimate would force all "
                + "of S_QQ to be zero, contradicting dimension one. Thus t!=0, "
                + "and star covariance gives star t=t.")),
            Paragraph(Text("Using the original Hilbert inner product, conjugate linear in "
                + "its first argument, define phi(z)=<t,z>/<t,t> on H. Then phi(t)=1 "
                + "and phi(z)t=z for every z in S_QQ, since its nonzero t spans this "
                + "one-dimensional space. Set b(Y,X)=phi(C(Q,Q)mu(star Y,X)), "
                + "beta=Re b(t,t) and alpha=Re<e,t>. The coefficient equation "
                + "b(Y,X)t=C(Q,Q)mu(star Y,X) holds for every Y,X in H. "
                + "Star covariance and star t=t give Hermitian sesquilinearity: "
                + "b is conjugate linear in Y, complex linear in X and "
                + "conj(b(Y,X))=b(X,Y).")),
            Paragraph(Text("Apply the unit-action estimate to t to obtain "
                + "|beta-1|<=219140r<1, hence beta>0. Square nondegeneracy at t "
                + "and Re<e,b(t,t)t>=alpha beta imply alpha>0. For every allowed P "
                + "and every X in S_PQ, b(X,X) is real nonnegative and equals zero "
                + "if and only if X=0. The original square identity and the support "
                + "error give (1-260000rM^2)||X||^2<=alpha b(X,X) "
                + "<=(1+260000rM^2)||X||^2. With d=delta+260000r, the operator-adjoint "
                + "square comparison instead gives (1-d)p(X)^2<=b(X,X)p(t) "
                + "<=(1+d)p(X)^2. In these real inequalities b(X,X) denotes its "
                + "real value. Neither alpha nor beta is set to one, and the regular "
                + "scale p(t) is retained.")))),
            new DocumentBlock.Section(H("Scalar column and pointwise adjoint directions"), Blocks(
            Paragraph(Text("For each allowed P, give a separate copy of S_PQ the inner "
                + "product b; its positivity and finite dimension give a Hilbert "
                + "space. H retains its original Hilbert structure. The scalar "
                + "column c->c t/sqrt(beta) is a complex-linear isometric embedding "
                + "from C into the copy of S_QQ. Without that normalization, "
                + "c->c t has coefficient norm squared beta|c|^2. The stated "
                + "isometric embedding carries no onto or column-saturation conclusion.")),
            Paragraph(Text("For any allowed P,R, every Z in S_PR, X in S_RQ and Y in S_PQ, "
                + "define F_Z(X)=C(P,Q)mu(Z,X) and "
                + "G_Z(Y)=C(R,Q)mu(star Z,Y). These are complex-linear maps between "
                + "the indicated separate corner Hilbert spaces. Taking adjoints "
                + "in that coefficient geometry, put h_PR(Z)=(F_Z+G_Z.adjoint)/2 "
                + "and h_RP(star Z)=(G_Z+F_Z.adjoint)/2. The reverse direction is "
                + "exactly h_PR(Z).adjoint, and the adjoint identity gives exactly "
                + "2b(Y,h_PR(Z)X)=b(C(R,Q)mu(star Z,Y),X) "
                + "+b(Y,C(P,Q)mu(Z,X)). This is a pointwise construction in Z. "
                + "It supplies no theorem of complex linearity in Z, multiplicativity, "
                + "a matrix representation or a block extension.")))),
            new DocumentBlock.Section(H("Degeneracies, provenance and remaining gaps"), Blocks(
            Paragraph(Text("All the universal estimates include zero allowed labels, zero "
                + "vectors, zero mixed-corner spaces, tau=delta=0, and equality at "
                + "the stated radius bounds. No extra nonzero-label or positive-error "
                + "hypothesis is imposed. The norm-one unit already excludes zero H. "
                + "The rank-one diagonal is a separate nontrivial input, with t!=0 "
                + "derived from it; existence or selection of a suitable Q from the "
                + "original product remains open. No identification with a separately "
                + "supplied old corner or old local map is established.")),
            Paragraph(Text("This application reuses the normalized scalar kernel above, "
                + "Mathlib's binomialSeries_radius_ge_one, "
                + "tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm, "
                + "Ring.add_choose_eq, geometric-series identities, "
                + "eq_span_singleton_of_mem_of_finrank_eq_one, "
                + "ContinuousLinearMap.adjoint_inner_right and norm_adjoint_comp_self, "
                + "and finite-dimensional linear adjoints. The Taylor construction "
                + "is that of Kitaev, Almost-idempotent quantum channels and "
                + "approximate C*-algebras, arXiv:2405.02434v2, equations (3.4)-(3.6) "
                + "and (7.1); the conditional corner route is in section 7 and "
                + "Lemma 9.4. No originality claim is made.")),
            Paragraph(Text("The project context is Q97.5, equations Q97.19-Q97.21 of "
                + "AURIC_COMPOSITE_COMPARISON_SAME_SCALE_PRODUCT_ORDER_STABILITY_V96_CONTINUATION. "
                + "Q97.21 uses the distinct global stability theorem 2.3 and "
                + "approximate-isomorphism definition 2.2 of Kitaev's paper. "
                + "The local conditional construction here does not prove that "
                + "global theorem or Q97.21. Selecting the rank-one Q, quantitative "
                + "action error and multiplicative defect for the symmetric maps, "
                + "compatible columns, dimension transfer, column surjectivity or "
                + "saturation, and a full block extension remain open. So do the "
                + "original finite-report and physical Gamma-to-Product bridge, "
                + "the full Q97.2 same-scale repair and full Q97 derivation.")))))))));
}
