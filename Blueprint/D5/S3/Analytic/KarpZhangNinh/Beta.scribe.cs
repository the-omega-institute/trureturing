using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangNinh;

internal sealed class BetaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangNinh/Beta.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta lifting preserves symmetric balancing for arbitrary real coefficients.",
        H("Symmetric homogeneous beta lifting"), Blocks(
            Paragraph(Text("The degree N and coefficient function c are arbitrary. No coefficient sign assumption is imposed. The homogeneous polynomial is evaluated on a line of fixed coordinate sum, and its lift replaces the powers by rising factorials.")),
            Entry("polynomial", "Homogeneous monomial expansion", DescribeRole.Definition,
                BindCoefficients(All("x", Rl(), All("y", Rl(), Eq(Poly(V("x"), V("y")),
                    Sum("k", Range(), Mul(Mul(Call("c", V("k")), Pow(V("x"), V("k"))),
                        Pow(V("y"), Sub(V("N"), V("k"))))))))),
                "The polynomial is the finite sum of c(k)x^k y^(N-k), including both endpoints."),
            Entry("lift", "Rising factorial lift", DescribeRole.Definition,
                BindCoefficients(All("u", Rl(), All("v", Rl(), Eq(Lift(V("u"), V("v")),
                    Sum("k", Range(), Mul(Mul(Call("c", V("k")), Poch(V("k"), V("u"))),
                        Poch(Sub(V("N"), V("k")), V("v")))))))),
                "The same coefficient array multiplies the two complementary rising factorials."),
            Entry("polynomial_continuous", "Continuity of the homogeneous slice", DescribeRole.Theorem,
                BindCoefficients(Call("Continuous", Slice())),
                "Every homogeneous slice is continuous because it is a finite sum of products of integer powers."),
            Entry("lift_continuous", "Continuity of the lifted slice", DescribeRole.Theorem,
                BindCoefficients(All("S", Rl(), Call("Continuous", LiftSlice()))),
                "The lifted slice is a polynomial in its real parameter, so it is continuous on the full real line."),
            Entry("polynomial_symm", "Symmetry of the homogeneous expansion", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), All("x", Rl(), All("y", Rl(),
                    Eq(Poly(V("x"), V("y")), Poly(V("y"), V("x"))))))),
                "Reflection of the finite index k to N-k proves coordinate symmetry when the coefficients are symmetric."),
            Entry("lift_symm", "Symmetry of the rising factorial expansion", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), All("u", Rl(), All("v", Rl(),
                    Eq(Lift(V("u"), V("v")), Lift(V("v"), V("u"))))))),
                "The same reflected finite sum proves symmetry of the lifted polynomial."),
            Entry("lift_eq_betaMean", "Normalized beta moment identity", DescribeRole.Theorem,
                BindCoefficients(All("m", Rl(), All("d", Rl(),
                    Imp(Lt(D(0), Add(V("m"), V("d"))), Imp(Lt(D(0), Sub(V("m"), V("d"))),
                        Eq(Lift(Add(V("m"), V("d")), Sub(V("m"), V("d"))),
                            Mul(Poch(V("N"), Mul(D(2), V("m"))),
                                BetaMean(Slice(), V("m"), V("d"))))))))),
                "Integrating each monomial against the beta density gives its Gamma quotient. KummerRatio.BetaIntegral.gamma_pochhammer converts the shifted Gamma factors to rising factorials. The remaining normalizer depends only on the total shape parameter."),
            Entry("betaMean_antiOn", "Weak comparison for arbitrary monotone integrands", DescribeRole.Theorem,
                All("W", Arrow(Rl(), Rl()), Imp(Call("ContinuousOn", V("W"), Interval("Icc", D(0), D(1))),
                    Imp(All("t", Rl(), Imp(Member(V("t"), Interval("Icc", D(0), D(1))),
                        Eq(Call("W", Sub(D(1), V("t"))), Call("W", V("t"))))),
                        Imp(Call("MonotoneOn", V("W"), HalfInterval()),
                            All("m", Rl(), Imp(Lt(D(0), V("m")),
                                Call("AntitoneOn", Lambda("d", BetaMean(V("W"), V("m"), V("d"))),
                                    Interval("Ico", D(0), V("m"))))))))),
                "Adding a positive multiple of t(1-t) makes the integrand strictly increasing toward the midpoint while preserving its symmetry. IncompleteBeta.Comparison.betaMean_strictAntiOn compares the perturbed means. Linearity of the integral and the limit as the perturbation decreases to zero yield the weak comparison."),
            Entry("lift_monotoneOn", "Beta lifting preserves balancing", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), Imp(Call("MonotoneOn", Slice(), HalfInterval()),
                    All("S", Rl(), Imp(Le(D(0), V("S")),
                        Call("MonotoneOn", LiftSlice(), Interval("Icc", D(0), Frac(V("S"), D(2))))))))),
                "For positive shapes, the beta moment identity and comparison of symmetric beta means show that the lift increases toward equal coordinates. Continuity extends the inequality to shape zero. A zero total has only the point zero. This preservation theorem has no positivity hypothesis on c."))));

    private static DocumentBlock Entry(string declaration, string title, DescribeRole role, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("karp-zhang-ninh-beta-" + declaration.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Rl() => Seq(Mathbb, Grp(V("R")));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) => Par(Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, Rl())), Sp, Mapsto, Sp, body));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Interval(string kind, Formula a, Formula b) => App(Q("Set", kind), a, b);
    private static Formula HalfInterval() => Interval("Ioc", D(0), Frac(D(1), D(2)));
    private static Formula Range() => App(Q("Finset", "range"), Add(V("N"), D(1)));
    private static Formula Poly(Formula x, Formula y) => Call("polynomial", V("c"), V("N"), x, y);
    private static Formula Lift(Formula u, Formula v) => Call("lift", V("c"), V("N"), u, v);
    private static Formula Poch(Formula n, Formula u) => App(Q("Polynomial", "eval"), u, Call("ascPochhammer", Rl(), n));
    private static Formula Slice() => Lambda("t", Poly(V("t"), Sub(D(1), V("t"))));
    private static Formula LiftSlice() => Lambda("s", Lift(V("s"), Sub(V("S"), V("s"))));
    private static Formula BetaMean(Formula w, Formula m, Formula d) => Call("betaMean", w, m, d);
    private static Formula CoefficientSymmetry() => All("k", N(), Imp(Le(V("k"), V("N")), Eq(Call("c", Sub(V("N"), V("k"))), Call("c", V("k")))));
    private static Formula BindCoefficients(Formula body) => All("c", Arrow(N(), Rl()), All("N", N(), body));
    private static Formula Sum(string name, Formula domain, Formula body) => Seq(F.Sum, Underscore, Grp(Seq(V(name), Sp, InMacro, Sp, domain)), Sp, Par(body));
}
