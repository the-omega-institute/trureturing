using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class SignedPrimePrimitiveCriterionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeta zeros and the signed prime tail primitive",
        H("An exponential growth bound and an exact slope criterion"),
        Blocks(
            Paragraph(Text("Write θ for the Chebyshev count with weight log p at each prime p. "
                + "The tail is integrated all the way to infinity. Both the tail and the outer interval "
                + "integral keep the signs of their integrands.")),
            Describe.Lean(DescribeId.Create("signed-prime-primitive"),
                DeclarationHandle.Create(Module + "signedPrimePrimitive"),
                H("The signed primitive of the actual prime tail"),
                StatementSource.FromAuthor(F.Disp(F.Seq(TailDefinition(), F.Qquad, PrimitiveDefinition()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inner integral is the set integral on (x,∞). The outer integral "
                    + "is the oriented interval integral with lower endpoint 2 and upper endpoint exp(T)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-primitive-exponent-bound"),
                DeclarationHandle.Create(Module + "HasExponentBound"),
                H("Eventual growth with arbitrary positive slack"),
                StatementSource.FromAuthor(F.Disp(new Formula.Logic(
                    Call("HasExponentBound", F.Id("b"), F.Id("f")), FormulaLogicOperator.Iff,
                    ExponentBound(F.Id("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameter b is real and f maps reals to reals. The constant "
                    + "and the eventual threshold can depend on the positive slack e."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zeta-zero-bound-from-signed-primitive"),
                DeclarationHandle.Create(Module + "zeta_zero_re_le_of_signedPrimePrimitive_exponent"),
                H("The growth hypothesis bounds every zero's real part"),
                StatementSource.FromAuthor(F.Disp(ZeroBound())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each fixed 1/2 ≤ β < 1 (written b in the formulas), an eventual bound "
                    + "on the signed primitive at exponential rate β+ε−1/2 for every ε>0 excludes zeta zeros with real part greater "
                    + "than β. The prime-power correction to the primitive is at most linear in T. "
                    + "This gives the same growth condition for the complete primitive. Integration by parts "
                    + "continues the Mangoldt transform to Re(s)>β. There the pole-removed zeta function "
                    + "satisfies a first-order analytic equation and is nonzero at s=2, so it stays nonzero "
                    + "on the half-plane."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-exact-signed-prime-slope"),
                DeclarationHandle.Create(Module + "rh_iff_signedPrimePrimitive_slope_from_5040"),
                H("The Riemann hypothesis and slope minus two from 5040"),
                StatementSource.FromAuthor(F.Disp(SlopeCriterion())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The endpoints in the criterion are the real number 5040 and exp(T). "
                        + "The divisor is T. The complete Chebyshev tail minus thetaTail(x), multiplied by √x, "
                        + "tends to +2 because of the actual prime powers. "
                        + "Under RH the oscillatory complete zero series has mean zero and its residual "
                        + "tends to zero. Subtracting the prime-power contribution gives prime-only slope −2. "
                        + "Moving the lower endpoint from 2 to 5040 changes the unnormalized integral by a fixed "
                        + "amount for large T, which vanishes after division by T.")),
                    Paragraph(Text("Conversely, the limit gives a linear bound for the signed primitive from 2. "
                        + "Apply the growth theorem at β=1/2 and use the functional equation to obtain RH."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Half => new Formula.Fraction(F.D(1), F.D(2));

    private static Formula Integral(Formula lower, Formula upper, Formula integrand, string variable) =>
        F.Seq(F.Int, F.Underscore, F.Grp(lower), F.Caret, F.Grp(upper), integrand,
            F.Thin, F.Id("d"), F.Id(variable));

    private static Formula TailDefinition()
    {
        var u = F.Id("u");
        var x = F.Id("x");
        return Equal(Call("thetaTail", x), Integral(x, F.Infty,
            new Formula.Fraction(Subtract(F.Seq(F.Theta, F.Open, u, F.Close), u),
                F.Seq(u, F.Caret, F.Grp(F.D(2)))), "u"));
    }

    private static Formula Window(Formula lower) =>
        Integral(lower, Call("exp", F.Id("T")),
            new Formula.Fraction(Call("thetaTail", F.Id("x")), F.Seq(F.Sqrt, F.Grp(F.Id("x")))), "x");

    private static Formula PrimitiveDefinition() => Equal(Call("P", F.Id("T")), Window(F.D(2)));

    private static Formula ExponentBound(Formula function)
    {
        var epsilon = F.Id("e");
        var constant = F.Id("C");
        var time = F.Id("T");
        var rate = Subtract(Add(F.Id("b"), epsilon), Half);
        var bound = Le(new Formula.Absolute(F.Seq(function, F.Open, time, F.Close)),
            F.Seq(constant, F.Thin, Call("exp", Multiply(F.Seq(F.Open, rate, F.Close), time))));
        return All("e", Real, Implies(Lt(F.D(0), epsilon),
            Exists("C", And(Le(F.D(0), constant),
                Exists("Y", All("T", Real, Implies(Le(F.Id("Y"), time), bound)))))));
    }

    private static Formula ZeroBound()
    {
        var beta = F.Id("b");
        var rho = F.Id("r");
        var realPart = F.Seq(F.Re, F.Open, rho, F.Close);
        return All("b", Real, Implies(And(And(Le(Half, beta), Lt(beta, F.D(1))),
            Call("HasExponentBound", beta, F.Id("P"))),
            All("r", Complex, Implies(Equal(F.Seq(F.Zeta, F.Open, rho, F.Close), F.D(0)),
                Le(realPart, beta)))));
    }

    private static Formula SlopeCriterion()
    {
        var limit = F.Seq(F.Lim, F.Underscore, F.Grp(F.Seq(F.Id("T"), F.To, F.Infty)),
            new Formula.Fraction(Window(F.D(5, 0, 4, 0)), F.Id("T")));
        return new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff,
            Equal(limit, new Formula.Negate(F.D(2))));
    }
}
