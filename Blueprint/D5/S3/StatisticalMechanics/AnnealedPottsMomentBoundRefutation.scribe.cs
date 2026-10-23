using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class AnnealedPottsMomentBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/janssen2025annealedpotts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mixture of two uniform densities has a unique positive Potts criticality zero below the proposed general moment lower bound.",
        H("A counterexample to the general Potts moment lower bound"),
        Blocks(
            Paragraph(Text(
                "All integrals are Lebesgue integrals on the real line. The parameter q is real, "
                    + "and the proposed inequality concerns q > 2. The functions F0 and K are the "
                    + "size-biased order parameter and criticality function of Section 1, equations (1) "
                    + "and (6), in Janssen's analysis of the annealed Potts model. The claim below is "
                    + "the general moment lower inequality in equation (84), with the standing curvature assumption "
                    + "and unique-positive-zero condition explicit.")),
            Node("moment", "Moments of a density", MomentFormula(),
                "These are the standard moments μₙ of a real-valued density f, with n a natural number. "
                    + "The definition uses the Lebesgue integral on the whole real line; for densities "
                    + "supported on positive weights it agrees with the integral over positive weights. "
                    + "The definition is total, and the proposed inequality supplies integrability conditions.",
                DescribeRole.Definition),
            Node("F0", "The size-biased order parameter", F0Formula(),
                "Equation (1) defines 𝓕₀ by the size-biased expectation, normalized by the first moment. "
                    + "The definition takes arbitrary real q and t; the proposed inequality uses q > 2 "
                    + "and positive zeros t.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("K", "The criticality function", KFormula(),
                "Equation (6) defines 𝒦 as the logarithmic expectation divided by the first moment, "
                    + "minus the two displayed correction terms, after eliminating the stationarity parameter.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed universal lower inequality", ClaimFormula(),
                "The lower inequality proposed in equation (84) asserts 2(μ₃/μ₄) ln(q − 1) < t "
                    + "at every positive zero t of 𝒦, for every real q > 2. "
                    + "The hypotheses require an integrable nonnegative density, zero for w ≤ 0, of total mass one, "
                    + "and with integrable fourth-moment integrand. The standing assumption requires a positive s "
                    + "such that 𝓕₀''(t) > 0 for 0 < t < s and 𝓕₀''(t) < 0 for t > s. "
                    + "They also require exactly one positive zero of 𝒦. "
                    + "The existential clause below includes the universal equality condition expressing uniqueness.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("density", "Two narrow uniform blocks", DensityFormula(),
                "Each indicator is one on the displayed closed interval and zero elsewhere. Multiplication by 500 "
                    + "makes each block have mass one. The mixture weights are 1331/1340 and 9/1340, "
                    + "and the block centers are 1 and 11. This density is nonnegative, has mass one, "
                    + "vanishes on nonpositive weights, and has finite moments of every natural order.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("potts-moment-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal inequality fails"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take q = 3 and the displayed two-block density f. Its first, third, and fourth moments "
                            + "are μ₁ = 143/134, μ₃ = 1331000143/134000000, and "
                            + "μ₄ = 33275001210000067/335000000000000. Set T = 6931/50000 = 0.13862. "
                            + "These exact moments and a lower bound for ln 2 give T < 2(μ₃/μ₄) ln 2.")),
                    Paragraph(Text(
                        "The second derivative of x ↦ (eˣ − 1)/(eˣ + 2) is "
                            + "3eˣ(2 − eˣ)/(eˣ + 2)³, positive for x < ln 2 and negative for x > ln 2. "
                            + "The second derivative 𝓕₀''(t) is its expectation at tW, weighted by W³/μ₁. "
                            + "This weighted expectation strictly decreases on [0, 9/50] and is positive at zero. "
                            + "On [9/50, 7/10], certified rational exponential enclosures on 26 subintervals "
                            + "make it negative; for t ≥ 7/10 both density intervals have tW > ln 2. "
                            + "Continuity therefore gives a positive s with 𝓕₀'' positive on (0, s) "
                            + "and negative on (s, ∞), as the standing assumption requires.")),
                    Paragraph(Text(
                        "Differentiating the criticality function gives "
                            + "𝒦'(t) = ((q − 1)/(2q))(𝓕₀(t) − t𝓕₀'(t)); at q = 3 this yields "
                            + "𝒦''(t) = −t𝓕₀''(t)/3. Since 𝒦(0) = 𝒦'(0) = 0 and 𝓕₀'' "
                            + "has exactly one positive zero, Rolle's theorem gives at most one positive zero of 𝒦. "
                            + "Near zero 𝒦 is negative. Rational exponential and logarithm bounds, with a symmetric "
                            + "integral error estimate for the two density intervals, give 𝒦(T) > 0. "
                            + "The intermediate value theorem supplies a positive zero at or below T, so the zero "
                            + "is unique and lies strictly below 2(μ₃/μ₄) ln 2. All the hypotheses hold "
                            + "while the proposed strict lower inequality fails."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("janssen-2025-annealed-potts-moment-lower-bound-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("potts-moment-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => name switch
    {
        "F0" => new Formula.Subscript(Seq(Mathcal, Grp(V("F"))), D(0)),
        "K" => Seq(Mathcal, Grp(V("K"))),
        _ => Seq(Operatorname, Grp(V(name))),
    };
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(x), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(x), Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Integral(string variable, Formula body) =>
        Seq(Int, Underscore, Grp(Real()), Sp, Parenthesized(body), Sp, Mathrm, Grp(V("d")), V(variable));
    private static Formula Lam(string x, Formula body) =>
        Seq(LambdaLower, Sp, Parenthesized(Seq(V(x), Colon, Sp, Real())), Sp, Mapsto, Sp,
            Parenthesized(body));
    private static Formula Moment(int n) => Call("moment", V("f"), D((byte)n));
    private static Formula ExpTW() => App(Exp, Mul(V("t"), V("w")));
    private static Formula FunctionBind(Formula body) => All("f", Arr(Real(), Real()), body);
    private static Formula ParameterBinds(Formula body) =>
        FunctionBind(All("q", Real(), All("t", Real(), body)));

    private static Formula MomentFormula() => FunctionBind(All("n", Nat(), Equal(
        Call("moment", V("f"), V("n")),
        Integral("w", Mul(Pow(V("w"), V("n")), App(V("f"), V("w")))))));

    private static Formula F0Formula() => ParameterBinds(Equal(Call("F0", V("f"), V("q"), V("t")),
        Div(Integral("w", Mul(Mul(V("w"), Div(Sub(ExpTW(), D(1)),
            Sub(Add(ExpTW(), V("q")), D(1)))), App(V("f"), V("w")))), Moment(1))));

    private static Formula KFormula() => ParameterBinds(Equal(Call("K", V("f"), V("q"), V("t")),
        Sub(Sub(Div(Integral("w", Mul(App(Log, Div(Sub(Add(ExpTW(), V("q")), D(1)), V("q"))),
                App(V("f"), V("w")))), Moment(1)),
            Mul(Mul(Div(Sub(V("q"), D(1)), Mul(D(2), V("q"))), V("t")),
                Call("F0", V("f"), V("q"), V("t")))), Div(V("t"), V("q")))));

    private static Formula PositiveZero(string x) => And(Less(D(0), V(x)),
        Equal(Call("K", V("f"), V("q"), V(x)), D(0)));

    private static Formula ClaimFormula()
    {
        Formula curvatureAtT = Call("iteratedDeriv", D(2), Call("F0", V("f"), V("q")), V("t"));
        Formula curvature = Some("s", Real(), And(Less(D(0), V("s")),
            And(All("t", Real(), Imp(Less(D(0), V("t")),
                    Imp(Less(V("t"), V("s")), Less(D(0), curvatureAtT)))),
                All("t", Real(), Imp(Less(V("s"), V("t")), Less(curvatureAtT, D(0)))))));
        Formula uniqueness = Some("u", Real(), And(PositiveZero("u"),
            All("s", Real(), Imp(PositiveZero("s"), Equal(V("s"), V("u"))))));
        Formula bound = All("t", Real(), Imp(Less(D(0), V("t")),
            Imp(Equal(Call("K", V("f"), V("q"), V("t")), D(0)),
                Less(Mul(Mul(D(2), Div(Moment(3), Moment(4))),
                    App(Log, Sub(V("q"), D(1)))), V("t")))));
        Formula[] hypotheses =
        [
            Call("Integrable", V("f")),
            All("w", Real(), Le(D(0), App(V("f"), V("w")))),
            All("w", Real(), Imp(Le(V("w"), D(0)), Equal(App(V("f"), V("w")), D(0)))),
            Equal(Integral("w", App(V("f"), V("w"))), D(1)),
            Call("Integrable", Lam("w", Mul(Pow(V("w"), D(4)), App(V("f"), V("w"))))),
            curvature,
            uniqueness,
        ];
        for (int i = hypotheses.Length - 1; i >= 0; i--) bound = Imp(hypotheses[i], bound);
        return IffOf(Named("claim"), All("q", Real(), Imp(Less(D(2), V("q")), FunctionBind(bound))));
    }

    private static Formula DensityFormula()
    {
        Formula Indicator(Formula left, Formula right) => App(new Formula.Subscript(
            Seq(Mathbf, Grp(D(1))), Seq(OpenBracket, left, Comma, Sp, right, CloseBracket)), V("w"));
        Formula first = Mul(D(5, 0, 0), Indicator(Div(D(9, 9, 9), D(1, 0, 0, 0)),
            Div(D(1, 0, 0, 1), D(1, 0, 0, 0))));
        Formula second = Mul(D(5, 0, 0), Indicator(Div(D(1, 0, 9, 9, 9), D(1, 0, 0, 0)),
            Div(D(1, 1, 0, 0, 1), D(1, 0, 0, 0))));
        return All("w", Real(), Equal(Call("density", V("w")),
            Add(Mul(Div(D(1, 3, 3, 1), D(1, 3, 4, 0)), Parenthesized(first)),
                Mul(Div(D(9), D(1, 3, 4, 0)), Parenthesized(second)))));
    }
}
