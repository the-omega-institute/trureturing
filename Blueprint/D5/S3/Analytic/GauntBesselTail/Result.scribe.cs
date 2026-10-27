using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GauntBesselTail;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/GauntBesselTail/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/gaunt2019besselintegrals");
    private static readonly LibraryNoteRef Dlmf = LibraryNoteRef.Create("D5/L/Asymptotics/nist2026dlmfbesselkintegral");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared-order convexity and an exact integral identity give the sharp weighted Bessel tail bound.",
        H("Gaunt's weighted Bessel tail inequality"), Blocks(
            Entry("alpha", Q("nu n", Eq(C("alpha", V("nu"), V("n")), Sub(Add(V("nu"), V("n")), Sqrt(Disc(V("nu"), V("n")))))), "The smaller parameter shift in Conjecture 2.4.", DescribeRole.Definition),
            Entry("alphaPrime", Q("nu n", Eq(C("alphaPrime", V("nu"), V("n")), Add(Add(V("nu"), V("n")), Sqrt(Disc(V("nu"), V("n")))))), "The second shift gives the opposite Bessel order.", DescribeRole.Definition),
            Entry("tail", Q("nu p x", Eq(Tail(V("nu"), V("p"), V("x")), Int(V("x"), "t", W(V("nu"), V("p"), V("t"))))), "The real power is used on the positive integration domain. The reused Bessel integral is DLMF 10.32.9.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gaunt-tail-claim"), DeclarationHandle.Create(Prefix + "claim"), H("The complete sharp tail assertion"), StatementSource.FromAuthor(Disp(Eq(V("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Conjecture 2.4, manuscript page 7 of arXiv:1806.00524v2, contains the verbatim fragments: “Then, for all x > 0,”, “We have equality in (2.17)” and “in inequality (2.17) is best possible, in the sense that, for any”. The displayed square roots and subscripts are reconstructed in the formula above. The conjunction preserves the source parameter range, its strict inequality, the either/or optimality for every beta outside the two named shifts, and the n=1 equality for every real nu. The reused K is exactly the positive-argument integral representation in DLMF 10.32.9. The tail uses t^(−nu) on t>x>0."))), DescribeRole.Definition),
            Entry("sinh_gap_pos", Q("v", Imp(Lt(D(0), V("v")), Lt(D(0), Sub(Mul(V("v"), Ch(V("v"))), Sh(V("v")))))), "The derivative is v sinh(v), strictly positive for v>0. This proves squared-order convexity."),
            Entry("cosh_sqrt_deriv", Q("u s", Imp(Lt(D(0), V("s")), Deriv(Lam("s", Ch(Mul(V("u"), Sqrt(V("s"))))), Mul(Div(V("u"), Mul(D(2), Sqrt(V("s")))), Sh(Mul(V("u"), Sqrt(V("s"))))), V("s")))), "The chain rule differentiates the squared-order kernel away from s=0."),
            Entry("cosh_sqrt_deriv2", Q("u s", Imp(Lt(D(0), V("s")), Deriv(Lam("s", Mul(Div(V("u"), Mul(D(2), Sqrt(V("s")))), Sh(Mul(V("u"), Sqrt(V("s")))))), Mul(Div(V("u"), Mul(D(4), Pow(Sqrt(V("s")), D(3)))), Sub(Mul(Mul(V("u"), Sqrt(V("s"))), Ch(Mul(V("u"), Sqrt(V("s"))))), Sh(Mul(V("u"), Sqrt(V("s")))))), V("s")))), "A second differentiation exposes the positive hyperbolic gap."),
            Entry("squared_order_strictConvex", Q("u", Imp(Lt(D(0), V("u")), C("StrictConvexOn", R, C("Set.Ici", D(0)), Lam("s", Ch(Mul(V("u"), Sqrt(V("s")))))))), "Continuity at zero and positivity of the second derivative prove strict convexity on the closed nonnegative half-line."),
            Entry("cosh_sqrt_sq", Q("u a", Imp(Le(D(0), V("u")), Eq(Ch(Mul(V("u"), Sqrt(Sq(V("a"))))), Ch(Mul(V("a"), V("u")))))), "Evenness removes the absolute value of the order."),
            Entry("positive_order_kernel", Q("u p q nu", Imp(Lt(D(0), V("u")), Imp(Lt(D(0), V("q")), Imp(Lt(V("q"), V("nu")), Imp(Eq(Sq(V("p")), Add(Add(Sq(V("q")), Mul(D(2), V("nu"))), D(1))), Lt(Add(Mul(Ch(Mul(V("q"), V("u"))), Ch(V("u"))), Mul(Mul(Div(V("nu"), V("q")), Sh(Mul(V("q"), V("u")))), Sh(V("u")))), Ch(Mul(V("p"), V("u"))))))))), "Compare adjacent secant slopes at (q−1)², (q+1)² and p². Hyperbolic addition then gives the sharp strict kernel inequality."),
            Entry("zero_order_kernel", Q("u p nu", Imp(Lt(D(0), V("u")), Imp(Lt(D(0), V("nu")), Imp(Eq(Sq(V("p")), Add(Mul(D(2), V("nu")), D(1))), Lt(Add(Ch(V("u")), Mul(Mul(V("nu"), V("u")), Sh(V("u")))), Ch(Mul(V("p"), V("u")))))))), "At q=0 use the tangent at s=1 instead of the two distinct secants."),
            Entry("parameters", Q("nu n", Imp(Lt(V("n"), D(1)), Imp(Le(Add(Sub(D(1), V("n")), Sqrt(Mul(D(2), Sub(D(1), V("n"))))), V("nu")), And(Le(D(0), Disc(V("nu"), V("n"))), And(Lt(Sqrt(Disc(V("nu"), V("n"))), V("nu")), Lt(Add(Sqrt(Disc(V("nu"), V("n"))), D(1)), Add(V("nu"), V("n")))))))), "The source parameter range gives a nonnegative discriminant, q<nu and q+1<nu+n."),
            Entry("cosh_quadratic", Q("u", Le(Add(D(1), Div(Sq(V("u")), D(2))), Ch(V("u")))), "The even-factorial-sum bound at length two supplies the quadratic lower bound."),
            Entry("exponential_kernel_integrable", Q("z A", Imp(Lt(D(0), V("z")), C("MeasureTheory.Integrable", Lam("u", Exp(Add(Mul(Neg(V("z")), Ch(V("u"))), Mul(V("A"), V("u")))))))), "A tilted integrable Gaussian dominates the exponential kernel on the whole real line."),
            Entry("bessel_kernel_integrable", Q("r z", Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(Kernel(V("z"), V("u")), Ch(Mul(V("r"), V("u"))))), D(0)))), "Expand cosh as a sum of exponentials and apply Gaussian domination for both signs of the order."),
            Entry("bessel_cosh_integrable", Q("r z", Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(Mul(Kernel(V("z"), V("u")), Ch(V("u"))), Ch(Mul(V("r"), V("u"))))), D(0)))), "The product of the two coshes is the half-sum of the adjacent-order coshes."),
            Entry("bessel_hasDerivAt", Q("r z", Imp(Lt(D(0), V("z")), Deriv(C("D5.S3.Analytic.GammaGammaNBU.Result.besselK", V("r")), Neg(Int(D(0), "u", Mul(Mul(Kernel(V("z"), V("u")), Ch(V("u"))), Ch(Mul(V("r"), V("u")))))), V("z")))), "Local domination with argument z/2 justifies differentiation under the integral."),
            Entry("integral_decay", All("f", Arr, Imp(All("u", R, Imp(Lt(D(0), V("u")), Le(D(0), C("f", V("u"))))), Imp(All("z", R, Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(Kernel(V("z"), V("u")), C("f", V("u")))), D(0)))), All("t", R, Imp(Le(D(1), V("t")), Le(Abs(Int(D(0), "u", Mul(Kernel(V("t"), V("u")), C("f", V("u"))))), Mul(Exp(Div(Neg(V("t")), D(2))), Int(D(0), "u", Mul(Kernel(Div(D(1), D(2)), V("u")), C("f", V("u"))))))))))), "For t≥1, cosh(u)≥1 splits off a uniform exp(−t/2) factor."),
            Entry("bessel_bigO", Q("r", BigO(C("D5.S3.Analytic.GammaGammaNBU.Result.besselK", V("r")))), "The positive Bessel kernel inherits the uniform exponential decay."),
            Entry("weighted_decay", All("F", Arr, Imp(C("ContinuousOn", V("F"), C("Set.Ioi", D(0))), Imp(BigO(V("F")), Q("nu x", Imp(Lt(D(0), V("x")), And(Integrable(Lam("t", Mul(Pow(V("t"), Neg(V("nu"))), C("F", V("t")))), V("x")), Limit(Lam("t", Mul(Pow(V("t"), Neg(V("nu"))), C("F", V("t"))))))))))), "Any real power times the exponentially decreasing function is integrable on every positive tail and tends to zero."),
            Entry("tail_integrable", Q("nu r x", Imp(Lt(D(0), V("x")), Integrable(Lam("t", W(V("nu"), V("r"), V("t"))), V("x")))), "The weighted Bessel kernel satisfies the hypotheses of weighted_decay."),
            Entry("weighted_bessel_tendsto", Q("nu r", Limit(Lam("t", W(V("nu"), V("r"), V("t"))))), "The weighted Bessel function vanishes at positive infinity."),
            Entry("abs_sinh_le_cosh", Q("u", Le(Abs(Sh(V("u"))), Ch(V("u")))), "Apply sinh(u)<cosh(u) at u and −u. This bounds the integration-by-parts kernel."),
            Entry("bessel_sinh_integrable", Q("r z", Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(Mul(Kernel(V("z"), V("u")), Sh(Mul(V("r"), V("u")))), Sh(V("u")))), D(0)))), "The absolute sinh product is bounded by the integrable cosh product."),
            Entry("exponential_kernel_tendsto", Q("z A", Imp(Lt(D(0), V("z")), Limit(Lam("u", Exp(Add(Mul(Neg(V("z")), Ch(V("u"))), Mul(V("A"), V("u")))))))), "The same quadratic domination also proves pointwise decay at infinity."),
            Entry("u_exponential_integrable", Q("z A", Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(V("u"), Exp(Add(Mul(Neg(V("z")), Ch(V("u"))), Mul(V("A"), V("u")))))), D(0)))), "The elementary bound u≤exp(u) absorbs the extra positive-domain factor."),
            Entry("u_exponential_tendsto", Q("z", Imp(Lt(D(0), V("z")), Limit(Lam("u", Mul(V("u"), Kernel(V("z"), V("u"))))))), "Absorb u into exp(u) and use the exponential-kernel limit."),
            Entry("S", Q("r u", Eq(C("S", V("r"), V("u")), C("ite", Eq(V("r"), D(0)), V("u"), Div(Sh(Mul(V("r"), V("u"))), V("r"))))), "This continuous-order antiderivative treats r=0 separately.", DescribeRole.Definition),
            Entry("S_deriv", Q("r u", Deriv(C("S", V("r")), Ch(Mul(V("r"), V("u"))), V("u"))), "For every real r, the derivative in u of S_r is cosh(ru)."),
            Entry("S_sinh_integrable", Q("r z", Imp(Lt(D(0), V("z")), Integrable(Lam("u", Mul(Mul(Kernel(V("z"), V("u")), C("S", V("r"), V("u"))), Sh(V("u")))), D(0)))), "The nonzero-order case follows from the sinh-product bound; the zero-order case uses the extra-u envelope."),
            Entry("S_kernel_tendsto", Q("r z", Imp(Lt(D(0), V("z")), Limit(Lam("u", Mul(Kernel(V("z"), V("u")), C("S", V("r"), V("u"))))))), "The boundary term in the hyperbolic integration by parts tends to zero."),
            Entry("bessel_ibp", Q("r z", Imp(Lt(D(0), V("z")), Eq(K(V("r"), V("z")), Mul(V("z"), Int(D(0), "u", Mul(Mul(Kernel(V("z"), V("u")), C("S", V("r"), V("u"))), Sh(V("u")))))))), "Differentiate exp(−z cosh u)S_r(u) and apply the fundamental theorem on the upper half-line."),
            Entry("H", Q("nu p r u", Eq(Hint(V("nu"), V("p"), V("r"), V("u")), Sub(Sub(Ch(Mul(V("p"), V("u"))), Mul(Ch(Mul(V("r"), V("u"))), Ch(V("u")))), Mul(Mul(V("nu"), C("S", V("r"), V("u"))), Sh(V("u")))))), "The signed kernel measures the difference between the tail and its proposed lower expression.", DescribeRole.Definition),
            Entry("J", Q("nu p r t", Eq(Jint(V("nu"), V("p"), V("r"), V("t")), Int(D(0), "u", Mul(Kernel(V("t"), V("u")), Hint(V("nu"), V("p"), V("r"), V("u")))))), "J is the Laplace integral of the signed kernel.", DescribeRole.Definition),
            Entry("H_integrable", Q("nu p r t", Imp(Lt(D(0), V("t")), Integrable(Lam("u", Mul(Kernel(V("t"), V("u")), Hint(V("nu"), V("p"), V("r"), V("u")))), D(0)))), "Each of the three terms is absolutely integrable."),
            Entry("J_eq", Q("nu p r t", Imp(Lt(D(0), V("t")), Eq(Jint(V("nu"), V("p"), V("r"), V("t")), Sub(Sub(K(V("p"), V("t")), Div(Add(K(Add(V("r"), D(1)), V("t")), K(Sub(V("r"), D(1)), V("t"))), D(2))), Mul(Div(V("nu"), V("t")), K(V("r"), V("t"))))))), "The adjacent-order identity and integration by parts express J using ordinary Bessel functions."),
            Entry("weighted_J_integrable", Q("nu p r x", Imp(Lt(D(0), V("x")), Integrable(Lam("t", Mul(Pow(V("t"), Neg(V("nu"))), Jint(V("nu"), V("p"), V("r"), V("t")))), V("x")))), "J_eq reduces this integrability to three weighted Bessel tails and one adjacent real power."),
            Entry("tail_identity", Q("nu p r x", Imp(Lt(D(0), V("x")), Eq(Sub(Tail(V("nu"), V("p"), V("x")), W(V("nu"), V("r"), V("x"))), Int(V("x"), "t", Mul(Pow(V("t"), Neg(V("nu"))), Jint(V("nu"), V("p"), V("r"), V("t"))))))), "Differentiate x^(−nu)K_r(x), integrate its derivative on the positive upper half-line, and use its zero limit."),
            Entry("integral_Ioi_pos", All("f", Arr, All("a", R, Imp(Integrable(V("f"), V("a")), Imp(All("u", R, Imp(Lt(V("a"), V("u")), Lt(D(0), C("f", V("u"))))), Lt(D(0), Int(V("a"), "u", C("f", V("u")))))))), "A positive integrand on an upper half-line has support of positive Lebesgue measure."),
            Entry("strict_tail", Q("nu p q x", Imp(Le(D(0), V("q")), Imp(Lt(V("q"), V("nu")), Imp(Eq(Sq(V("p")), Add(Add(Sq(V("q")), Mul(D(2), V("nu"))), D(1))), Imp(Lt(D(0), V("x")), Lt(W(V("nu"), V("q"), V("x")), Tail(V("nu"), V("p"), V("x")))))))), "The strict scalar kernel comparison makes J positive, and tail_identity then gives the strict bound."),
            Entry("n_one_identity", Q("nu x", Imp(Lt(D(0), V("x")), Eq(Tail(V("nu"), Add(V("nu"), D(1)), V("x")), W(V("nu"), V("nu"), V("x"))))), "The addition formula makes H identically zero when p=nu+1 and r=nu, including nu=0 and negative nu."),
            Entry("laplace_negative", All("f", Arr, Imp(All("t", R, Imp(Lt(D(0), V("t")), Integrable(Lam("u", Mul(Kernel(V("t"), V("u")), C("f", V("u")))), D(0)))), All("delta", R, Imp(Lt(D(0), V("delta")), Imp(All("u", R, Imp(Lt(D(0), V("u")), Imp(Lt(V("u"), V("delta")), Lt(C("f", V("u")), D(0))))), C("Filter.Eventually", Lam("t", Lt(Int(D(0), "u", Mul(Kernel(V("t"), V("u")), C("f", V("u")))), D(0))), C("Filter.atTop"))))))), "A negative interval next to the origin contributes at a slower exponential decay rate than the outer positive part. A fixed inner subinterval therefore forces a negative Laplace integral for every sufficiently large t."),
            Entry("H_negative_near", Q("nu p q r", Imp(Le(D(0), V("q")), Imp(Lt(V("q"), V("r")), Imp(Eq(Sq(V("p")), Add(Add(Sq(V("q")), Mul(D(2), V("nu"))), D(1))), Ex("delta", R, And(Lt(D(0), V("delta")), All("u", R, Imp(Lt(D(0), V("u")), Imp(Lt(V("u"), V("delta")), Lt(Hint(V("nu"), V("p"), V("r"), V("u")), D(0))))))))))), "At zero both H and its first derivative vanish, while its second derivative is q²−r²<0. The derivative test gives a negative right-hand interval."),
            Entry("larger_order_failure", Q("nu p q r", Imp(Le(D(0), V("q")), Imp(Lt(V("q"), V("r")), Imp(Eq(Sq(V("p")), Add(Add(Sq(V("q")), Mul(D(2), V("nu"))), D(1))), C("Filter.Eventually", Lam("x", Lt(Tail(V("nu"), V("p"), V("x")), W(V("nu"), V("r"), V("x")))), C("Filter.atTop")))))), "The local kernel sign and laplace_negative make J negative for all sufficiently large t. The tail identity proves failure at every sufficiently large x, stronger than a single positive witness."),
            Entry("bessel_order_lt", Q("a b x", Imp(Lt(Abs(V("a")), Abs(V("b"))), Imp(Lt(D(0), V("x")), Lt(K(V("a"), V("x")), K(V("b"), V("x")))))), "Strict increase of cosh in the absolute order and positive integration prove strict order monotonicity."),
            Describe.Lean(DescribeId.Create("gaunt-tail-result"), DeclarationHandle.Create(Prefix + "result"), H("The sharp bound and its optimality"), StatementSource.FromAuthor(Disp(V("claim"))), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The strict bound follows from squared-order convexity and the exact tail identity. A smaller absolute order gives a strictly smaller right side at every positive x; a larger absolute order fails for all sufficiently large x. The two excluded shifts give opposite orders and therefore identical Bessel values. When n=1, the hyperbolic addition formula makes the signed kernel identically zero for every real nu."))), DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("gaunt-2019-bessel-tail-conjecture"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Entry(string name, Formula statement, string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("gaunt-tail-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace('_', ' ')),
            StatementSource.FromAuthor(Disp(statement)),
            name == "alpha" || name == "alphaPrime" ? AssessedProvenance.FromLiterature(Source) :
            name == "tail" ? AssessedProvenance.FromRepo(Dlmf) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula Arr => new Formula.TypeArrow(R, R);
    private static Formula Q(string names, Formula body)
    {
        var variables = names.Split(' ');
        for (var i = variables.Length - 1; i >= 0; i--) body = All(variables[i], R, body);
        return body;
    }
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]);
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Or, P(b));
    private static Formula Lam(string n, Formula body) => Seq(V(n), Colon, Sp, R, Mapsto, Sp, body);
    private static Formula Int(Formula a, string n, Formula body) => C("MeasureTheory.integral", C("Measure.restrict", C("volume"), C("Set.Ioi", a)), Lam(n, body));
    private static Formula Exp(Formula a) => C("Real.exp", a);
    private static Formula Ch(Formula a) => C("Real.cosh", a);
    private static Formula Sh(Formula a) => C("Real.sinh", a);
    private static Formula Sq(Formula a) => Pow(a, D(2));
    private static Formula Sqrt(Formula a) => C("Real.sqrt", a);
    private static Formula Abs(Formula a) => C("abs", a);
    private static Formula K(Formula r, Formula x) => C("D5.S3.Analytic.GammaGammaNBU.Result.besselK", r, x);
    private static Formula W(Formula nu, Formula r, Formula x) => Mul(Pow(x, Neg(nu)), K(r, x));
    private static Formula Kernel(Formula t, Formula u) => Exp(Neg(Mul(t, Ch(u))));
    private static Formula Tail(Formula nu, Formula p, Formula x) => C("tail", nu, p, x);
    private static Formula Hint(Formula nu, Formula p, Formula r, Formula u) => C("H", nu, p, r, u);
    private static Formula Jint(Formula nu, Formula p, Formula r, Formula t) => C("J", nu, p, r, t);
    private static Formula Integrable(Formula f, Formula a) => C("MeasureTheory.IntegrableOn", f, C("Set.Ioi", a));
    private static Formula Limit(Formula f) => C("Filter.Tendsto", f, C("Filter.atTop"), C("nhds", D(0)));
    private static Formula BigO(Formula f) => C("Asymptotics.IsBigO", C("Filter.atTop"), f, Lam("t", Exp(Neg(Div(V("t"), D(2))))));
    private static Formula Deriv(Formula f, Formula df, Formula x) => C("HasDerivAt", f, df, x);
    private static Formula Disc(Formula nu, Formula n) => Sub(Sub(Sq(Add(nu, n)), Mul(D(2), nu)), D(1));
    private static Formula A(Formula nu, Formula n) => C("alpha", nu, n);
    private static Formula Aprime(Formula nu, Formula n) => C("alphaPrime", nu, n);
    private static Formula Range(Formula nu, Formula n) => And(Lt(n, D(1)), Le(Add(Sub(D(1), n), Sqrt(Mul(D(2), Sub(D(1), n)))), nu));
    private static Formula ClaimBody()
    {
        var nu = V("nu"); var n = V("n"); var x = V("x"); var beta = V("beta");
        var p = Add(nu, n); var q = Sub(p, A(nu, n));
        var first = Q("n nu", Imp(Range(nu, n), All("x", R, Imp(Lt(D(0), x), Lt(W(nu, q, x), Tail(nu, p, x))))));
        var second = Q("n nu", Imp(Range(nu, n), All("beta", R, Imp(And(Ne(beta, A(nu, n)), Ne(beta, Aprime(nu, n))),
            Or(All("x", R, Imp(Lt(D(0), x), Lt(W(nu, Sub(p, beta), x), W(nu, q, x)))),
                Ex("y", R, And(Lt(D(0), V("y")), Lt(Tail(nu, p, V("y")), W(nu, Sub(p, beta), V("y"))))))))));
        var third = Q("nu x", Imp(Lt(D(0), x), Eq(Tail(nu, Add(nu, D(1)), x), W(nu, nu, x))));
        return And(first, And(second, third));
    }
}
