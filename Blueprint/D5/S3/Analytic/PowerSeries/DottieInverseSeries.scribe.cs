using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class DottieInverseSeriesDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Endpoint() => new Formula.Bind(FormulaQuantifier.Exists,
        FormulaIdentifier.Create("theta"), F.Id("Real"), Seq(
            D(0), Sp, Lt, Sp, F.Id("theta"), Sp, Land, Sp,
            F.Id("theta"), Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Call("cos", F.Id("theta")), Sp, Eq, Sp, F.Id("theta"), Sp, Land, Sp,
            Seq(Open, All("t", F.Id("Real"), Seq(
                Seq(Open, D(0), Sp, Lt, Sp, F.Id("t"), Sp, Land, Sp,
                    Call("cos", F.Id("t")), Sp, Eq, Sp, F.Id("t"), Close), Sp, Implies, Sp,
                F.Id("t"), Sp, Eq, Sp, F.Id("theta"))), Close), Sp, Land, Sp,
            Call("Summable", Seq(F.Id("n"), Colon, Sp, F.Id("Nat"), Sp, Mapsto, Sp,
                Call("abs", Call("c", F.Id("n"))), Sp, Call("piPower", F.Id("n")))),
            Sp, Land, Sp,
            Call("HasSum", Seq(F.Id("n"), Colon, Sp, F.Id("Nat"), Sp, Mapsto, Sp,
                Call("c", F.Id("n")), Sp, Call("piPower", F.Id("n"))), F.Id("theta"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed rational inverse converges absolutely at pi to the unique positive cosine fixed point.",
        H("The prescribed rational inverse series"),
        Blocks(
            Describe.Lean(DescribeId.Create("dottie-arcsine-coefficients"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.alpha"),
                H("Rational coefficients in every degree"),
                StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), Seq(
                    Call("alpha", Seq(D(2), F.Id("n"))), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Call("alpha", Seq(D(2), F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp,
                    Call("div", Call("choose", Seq(D(2), F.Id("n")), F.Id("n")),
                        Seq(D(4), Caret, Grp(F.Id("n")), Open,
                            D(2), F.Id("n"), Sp, Plus, Sp, D(1), Close)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient sequence alpha takes values in the rationals. Its even coefficients vanish and its degree 2n+1 coefficient is choose(2n,n)/(4^n(2n+1)). The definition selects these cases using the parity and integer half of the input degree."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-arcsine-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.arcsine"),
                H("The formal rational arcsine series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("S"), Sp, Eq, Sp,
                    Call("mk", F.Id("alpha"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S denotes PowerSeries.mk alpha over the rationals. Its coefficient in degree zero is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-forward-series"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.forward"),
                H("The forward series"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Sp, Eq, Sp,
                    D(2), F.Id("X"), Sp, Plus, Sp, D(2), F.Id("S")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A is the literal rational formal series 2X+2S. Its constant coefficient is zero and its linear coefficient is 4, a unit in the rational field."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-prescribed-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.inverse"),
                H("The prescribed formal inverse"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("B"), Sp, Eq, Sp,
                    Call("substInvOfIsUnit", F.Id("A"), Call("unit", D(4)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B is exactly A.substInvOfIsUnit for the proof that the linear coefficient 4 is a unit. The choice of that proof does not alter the formal series."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dottie-rational-inverse-endpoint"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieInverseSeries.rational_inverse_endpoint"),
                H("Absolute convergence at pi and the positive fixed point"),
                StatementSource.FromAuthor(Disp(Endpoint())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/kaplan2007dottie")),
                Blocks(
                    Paragraph(Text("Here c(n) is the real image of coefficient n of the literal rational series B, and piPower(n) means pi raised to n. Every natural degree, including zero, is included; no coefficient sign is discarded in HasSum. The unique positive cosine fixed point theta lies strictly between zero and one. Competitors t are arbitrary positive real numbers; no upper bound on t is assumed.")),
                    Paragraph(Text("Kaplan describes the rational pi series and the inverse-Taylor construction. The present proof supplies the complete all-coefficient connection, a single analytic branch with radius exceeding pi, absolute convergence and the all-positive uniqueness conclusion. No novelty or priority claim is made."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Connecting the selected analytic inverse"), Blocks(
                Paragraph(Text("For a complex function H analytic at zero and real on the real axis near zero, let h(y)=Re(H(y)) for real y. The real_taylor_data lemma supplies real analyticity of h and the real and imaginary parts of every complex derivative coefficient, including degree zero. Its Taylor series T has coefficient iteratedDeriv(n,h,0)/n!.")),
                Paragraph(Text("Suppose H(0)=0, the real function a(x)=2x+2arcsin(x) has the expansion given by A mapped to the reals, and a(h(y))=y near zero. Then T has zero constant coefficient. The scalar composition correspondence identifies the expansion of a composed with h with the realization of A substituted by T. Uniqueness of one-dimensional analytic expansions makes that substitution equal X. The mapped rational series B is another right formal inverse, by map_subst. Formal inverse uniqueness therefore gives T equal to B mapped to the reals. The same real_taylor_data coefficients then identify every complex derivative coefficient of H with the complex image of the corresponding rational coefficient of B.")),
                Paragraph(Text("A selected function is obtained from f(z)=z+sin(z). For norm(z)<=1, the pinned sine and cosine remainder bounds give norm(sin(z)-z)<=1/5 and norm(cos(z)-1)<=3/5. For norm(w)<7/4, the map z maps to (w+z-sin(z))/2 preserves the closed unit disk and has Lipschitz constant 3/10. Banach fixed-point existence, together with the same contraction estimate for uniqueness, defines a single inverse G(w) in the open unit disk. The nonzero derivative and the existing analytic local inverse identify that selection with an analytic inverse near each w. Conjugation and uniqueness make G real on real arguments, and G(0)=0. Thus H(Y)=sin(G(Y/2)) is analytic for norm(Y)<7/2, preserves real arguments and vanishes at zero. Cauchy supplies an expansion on radius 13/4. Termwise integration of the original normalized binomial series supplies the prescribed arcsine expansion for abs(x)<1. The principal arcsine identity on the real unit interval then gives 2*Re(H(y))+2*arcsin(Re(H(y)))=y for abs(y)<7/2. The original real_taylor_data and the live scalar composition correspondence identify every coefficient of this same H with B; expansion uniqueness then identifies the full Cauchy expansion with the scalar realization of B. Since pi<13/4, the existing convergence-radius theorem proves summability of abs(c(n))*pi^n. Evaluation of that expansion at pi and taking real parts proves HasSum with the signed coefficients.")),
                Paragraph(Text("For x=Re(G(pi/2)), the branch equation gives x+sin(x)=pi/2 and abs(x)<1. Nonpositivity of x would force sin(x)<=0, contradicting pi>0. Thus x>0 and theta=sin(x) satisfies 0<theta<x<1. The branch equation also gives theta=pi/2-x, hence cos(theta)=theta. Any positive fixed point t satisfies t<=1 from cos(t)<=1; strict decrease of cosine from zero excludes t=1. Cosine is antitone on [0,pi], so two positive fixed points in (0,1) cannot differ. This proves the uniqueness clause without restricting competitors in the theorem statement.")))),
            new DocumentBlock.Section(H("A real cosine application of the endpoint"), Blocks(
                Paragraph(Text("All variables in this application are real, and angles are in radians. Define f(x)=cos(x) and g(x)=f(f(x))=cos(cos(x)). For a natural number n, f^[n] and g^[n] denote n-fold composition, with the zeroth iterate the identity. Choose theta from rational_inverse_endpoint above: the same theta satisfies 0<theta<1, cos(theta)=theta and the signed inverse-series sum at pi. No second fixed-point parameter is selected below. The displayed endpoint theorem concerns that series and positive competitors; the following dynamics are consequences of its fixed-point clauses and the real calculus and contraction results described here.")),
                Paragraph(Text("The uniqueness conclusion extends to all real competitors. If cos(t)=t, the cosine range gives -1<=t<=1. Since 1<pi/2, cosine is strictly positive throughout [-1,1], so t=cos(t)>0. The positive uniqueness clause of rational_inverse_endpoint now gives t=theta. In particular, theta is the only real fixed point of f, and 0<theta<1<pi/2 places this same point in the acute interval (0,pi/2). This extension uses the range bound to discharge positivity; it does not assume positivity of an arbitrary competitor.")),
                Paragraph(Text("The exact image of g is [cos(1),1]. Indeed, Real.range_cos identifies the inner cosine range with [-1,1]. Evenness reduces the outer cosine to its values on [0,1], where it is continuous and strictly decreasing from 1 to cos(1). The intermediate value theorem, in the form intermediate_value_Icc', supplies every value between those endpoints; each required inner argument is itself in the range of cosine. Thus this is equality of ranges, not merely an upper and lower bound. Because cos(1)>0 and 1<pi/2, [cos(1),1] is contained in (0,pi/2). For every real start z and every natural n, g^[n+1](z) belongs to both these intervals. The initial value g^[0](z)=z has no such restriction.")))),
            new DocumentBlock.Section(H("Global contraction and the mutual pair"), Blocks(
                Paragraph(Text("The chain rule, using Real.hasDerivAt_cos for each cosine, gives a derivative at every real x:"),
                    Math(Disp(Seq(F.Id("g"), Apos, Open, F.Id("x"), Close, Sp, Eq, Sp,
                        Call("sin", Call("cos", F.Id("x"))), Sp,
                        Call("sin", F.Id("x"))))),
                    Text("Here the prime denotes the derivative of g at x. The two negative signs from differentiating cosine cancel. For every real x, abs(cos(x))<=1 and abs(sin(x))<=1. On [0,1], sine is nonnegative and increasing, so abs(sin(cos(x)))=sin(abs(cos(x)))<=sin(1). Consequently abs(g'(x))<=sin(1) for every real x. Put K=sin(1); since 0<1<pi/2, 0<K<1. K is a sufficient global bound, with no assertion that it is the least possible bound.")),
                Paragraph(Text("The mean-value Lipschitz result lipschitzWith_of_nnnorm_deriv_le applies with domain and codomain the real normed space, function g, and nonnegative constant K. Its differentiability assumption is supplied by the chain rule, and its derivative-norm hypothesis is exactly the preceding all-real bound. It yields abs(g(u)-g(v))<=K*abs(u-v) for all real u,v. Thus g is ContractingWith K on the complete metric space of real numbers. The endpoint equation gives g(theta)=f(f(theta))=theta. ContractingWith.fixedPoint_unique' identifies every fixed point of g with this theta, and ContractingWith.tendsto_iterate_fixedPoint gives g^[n](z) tending to theta as n tends to infinity for every real z. There is no interval assumption on this convergence statement.")),
                Paragraph(Text("A mutual cosine pair means real numbers a,b satisfying a=cos(b) and b=cos(a). Substitution gives g(a)=a and g(b)=b. The contraction uniqueness result therefore forces a=theta and b=theta. Conversely, (theta,theta) satisfies both equations, so it is the unique real mutual pair. The pair and the attracting point of g are thereby identified with the inverse-series endpoint, rather than with separately chosen solutions.")),
                Paragraph(Text("For every real z and every natural n, g^[n](z)=f^[2*n](z). This is the composition identity Function.iterate_mul with g=f^[2]. Hence the even subsequence of the f orbit tends to theta. Its odd subsequence is f(f^[2*n](z)); continuity of cosine makes its limit f(theta)=theta. Combining the two parity subsequences proves f^[n](z) tending to theta for every real z. This argument proves all-real convergence without requiring f itself to have a global contraction constant strictly below one.")))),
            new DocumentBlock.Section(H("Order, strict alternation and exceptional starts"), Blocks(
                Paragraph(Text("Strict order properties require their own domains. For x in (0,pi/2), sin(x)>0 and 0<cos(x)<=1<pi, so sin(cos(x))>0. Thus g'(x)>0 on that open interval. The convex-domain result strictMonoOn_of_deriv_pos, with the continuity of g, makes g strictly increasing on (0,pi/2). This is a property of g on the acute interval, not a global order assertion about g on the real line.")),
                Paragraph(Text("Now let 0<y0<theta and write y_n=g^[n](y0). If 0<y<theta, strict increase of g on the acute interval and g(theta)=theta give g(y)<theta. The contraction inequality then reads theta-g(y)<=K*(theta-y)<theta-y, whence y<g(y). Induction gives 0<y_n<y_(n+1)<theta for every natural n, including n=0. The sequence is strictly increasing in its index and converges to theta by the all-real convergence result. The condition 0<y0<theta is retained in this strict increasing-orbit assertion; convergence from arbitrary real starts does not by itself imply this order pattern.")),
                Paragraph(Text("For the f orbit, assume instead x0 belongs to [0,1] and x0 is different from theta, and set x_n=f^[n](x0). Cosine maps [0,1] into [0,1] and is strictly decreasing there, by Real.strictAntiOn_cos restricted to that interval. Its resulting injectivity prevents a nonfixed point in [0,1] from mapping to theta, because f(theta)=theta. Induction therefore keeps every x_n in [0,1] and different from theta. For every natural n, x_n<theta if and only if theta<x_(n+1), and theta<x_n if and only if x_(n+1)<theta. Equivalently, (x_n-theta)*(x_(n+1)-theta)<0. These are strict alternation statements under the stated nonfixed interval hypothesis, alongside the already established convergence.")),
                Paragraph(Text("The starts theta and -theta must be treated explicitly. Evenness gives f(-theta)=f(theta)=theta, and consequently g(-theta)=g(theta)=theta. For every natural n, f^[n](theta)=g^[n](theta)=theta, while f^[n+1](-theta)=g^[n+1](-theta)=theta. The first start is stationary; the second reaches theta after one application of either map. Their subsequent errors are zero, so they do not exhibit strict alternation or nonzero-denominator error ratios. The strict claims above are confined to their specified starts; no exhaustive classification of real preimages of theta is needed or asserted.")))),
            new DocumentBlock.Section(H("Exact local error factors and iteration cost"), Blocks(
                Paragraph(Text("The fixed-point equation and the acute location determine the local factors exactly. Real.sin_eq_sqrt_one_sub_cos_sq applies with 0<theta<pi/2, and Real.sin_sq_add_cos_sq with cos(theta)=theta gives sin(theta)^2=1-theta^2. Positivity of sine selects the positive square root. The derivatives, including their derivative-existence statements, are therefore"),
                    Math(Disp(Seq(F.Id("f"), Apos, Open, Theta, Close, Sp, Eq, Sp,
                        Minus, Call("sin", Theta), Sp, Eq, Sp,
                        Minus, Sqrt, Grp(D(1), Sp, Minus, Sp, Theta, Caret, Grp(D(2))),
                        Comma, Sp, Minus, D(1), Sp, Lt, Sp, F.Id("f"), Apos, Open, Theta, Close, Sp, Lt, Sp, D(0)))),
                    Math(Disp(Seq(F.Id("g"), Apos, Open, Theta, Close, Sp, Eq, Sp,
                        Call("sin", Theta), Caret, Grp(D(2)), Sp, Eq, Sp,
                        D(1), Sp, Minus, Sp, Theta, Caret, Grp(D(2)),
                        Comma, Sp, D(0), Sp, Lt, Sp, F.Id("g"), Apos, Open, Theta, Close, Sp, Lt, Sp, D(1)))),
                    Text("As above, a prime denotes the derivative at the displayed argument. In particular g'(theta)=(f'(theta))^2. The negative f derivative describes reversal of the local signed error; the positive g derivative describes preservation of its sign.")),
                Paragraph(Text("These factors are limits of slopes, not identities for errors at a finite distance. For h equal to f or g, define the punctured slope at theta to be (h(x)-h(theta))/(x-theta) for x different from theta. HasDerivAt.tendsto_slope converts each derivative-existence statement into the corresponding limit as real x tends to theta through x different from theta. Since f(theta)=g(theta)=theta, this gives (f(x)-theta)/(x-theta) tending to -sin(theta)=-sqrt(1-theta^2), and (g(x)-theta)/(x-theta) tending to sin(theta)^2=1-theta^2. Both limits are along the full punctured real neighborhood, with no one-sided restriction.")),
                Paragraph(Text("To turn a punctured slope limit into an orbit error ratio, one must also ensure that the orbit never reaches theta. For x0 in [0,1] different from theta, the strict alternation argument gives x_n different from theta for every n. With e_n=x_n-theta, all denominators e_n are nonzero and all e_n*e_(n+1)<0. Composing the punctured f slope limit with this convergent orbit yields e_(n+1)/e_n tending to -sqrt(1-theta^2). For 0<y0<theta, write y_n=g^[n](y0) and d_n=y_n-theta. The strict bounds y_n<theta make every d_n negative and nonzero; composition with the punctured g slope limit yields d_(n+1)/d_n tending to 1-theta^2. The factors compare asymptotic signed errors under these respective initial conditions; the ratio claims are not extended to every real start.")),
                Paragraph(Text("The magnitude of the local f factor is sqrt(1-theta^2), whereas the local g factor is 1-theta^2, its square. Each lies strictly between zero and one. This comparison is per application of the chosen map: evaluating g(x)=cos(cos(x)) requires two cosine evaluations, while evaluating f(x) requires one. The exact identity g^[n](z)=f^[2*n](z) compares the same starting value after the same number of cosine evaluations. The squared factor therefore expresses two f steps grouped into one g step; it supplies no speedup per cosine evaluation or wall-clock resource bound.")),
                Paragraph(Text("The qualitative contraction uses only the coarse bound K=sin(1). A sharp global supremum of abs(g'), its maximizing arguments, the values approximately 0.461063 and 0.828132, and any displayed decimal constants require separate numerical or optimization certificates. The same applies to the finite n=0,...,5 iteration table starting at 1/10, its rounding and numerical error comparisons; those claims are not certified here. A candidate critical equation such as (1-t^2)*cos(t)=t*sin(t) is only a route toward an optimization argument, not a substitute for one. These real mathematical consequences neither certify the entire numerical example nor establish a physical, philosophical or ontological interpretation, a computational resource advantage, or a novelty claim.")))))));
}
