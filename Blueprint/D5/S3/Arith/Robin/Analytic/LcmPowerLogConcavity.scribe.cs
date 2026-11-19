using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerLogConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict logarithmic concavity of consecutive real power differences.",
        H("A logarithmically concave power difference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-power-difference"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference"),
                H("The difference of consecutive powers"),
                StatementSource.FromAuthor(DifferenceDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real kappa and t define C(kappa,t)=(1+t)^kappa-t^kappa. "
                    + "The powers are real powers. This is a total real-valued definition; "
                    + "the concavity conclusion below assumes kappa>1 and t>=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-unit-power-difference"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference"),
                H("The logarithmic difference"),
                StatementSource.FromAuthor(LogDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "B(kappa,t) is the total real logarithm of C(kappa,t). "
                    + "For kappa>1 and t>=0 the power difference is strictly positive, "
                    + "so this logarithm has its ordinary positive-argument interpretation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("power-difference-positive"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.difference_pos"),
                H("Positivity of the power difference"),
                StatementSource.FromAuthor(PositivityClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For kappa>1 and t>=0, strict increase of positive real powers gives C(kappa,t)>0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-power-difference-derivative"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.log_derivative"),
                H("The logarithmic derivative"),
                StatementSource.FromAuthor(DerivativeClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For kappa>1 and t>0, B has the displayed derivative. The power difference "
                    + "is positive, so the logarithmic chain rule applies. This derivative "
                    + "also supplies the elasticity used to compare the F equation solutions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-difference-curvature"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.powerDifference_curvature"),
                H("The exact curvature identity"),
                StatementSource.FromAuthor(CurvatureClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real kappa and every t>0 the displayed derivative identity holds. "
                    + "It follows from C'(t)=kappa*((1+t)^(kappa-1)-t^(kappa-1)) and "
                    + "C''(t)=kappa*(kappa-1)*((1+t)^(kappa-2)-t^(kappa-2)). "
                    + "Positivity of kappa-1 is needed only for the subsequent concavity conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-power-difference-concavity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLogConcavity.logPowerDifference_concavity"),
                H("Strict concavity and the zero endpoint"),
                StatementSource.FromAuthor(ConcavityClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real kappa>1, B(kappa,.) is strictly concave on the open "
                        + "positive half-line and concave on the closed nonnegative half-line, "
                        + "and its value at zero is zero. No upper bound on kappa is assumed.")),
                    Paragraph(Text(
                        "Write D(t)=(1+t)^(kappa-1)-t^(kappa-1). On t>0 the exact identity "
                        + "(C'(t))^2-C(t)*C''(t)=kappa*D(t)^2"
                        + "+kappa*(kappa-1)*(t*(1+t))^(kappa-2) has a strictly positive "
                        + "right-hand side. The quotient formula for the second derivative "
                        + "of log(C) therefore gives B''<0. Continuity at zero extends the "
                        + "concavity to the closed half-line, and C(kappa,0)=1 gives B(kappa,0)=0."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesClaim(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula DifferenceDefinition()
    {
        var k = F.Id("kappa");
        var t = F.Id("t");
        return Disp(All("kappa", Real, All("t", Real,
            Equal(Call("powerDifference", k, t), Subtract(Pow(Add(D(1), t), k), Pow(t, k))))));
    }

    private static Formula LogDefinition()
    {
        var k = F.Id("kappa");
        var t = F.Id("t");
        return Disp(All("kappa", Real, All("t", Real,
            Equal(Call("logPowerDifference", k, t), Call("log", Call("powerDifference", k, t))))));
    }

    private static Formula PositivityClaim()
    {
        var k = F.Id("kappa");
        var t = F.Id("t");
        return Disp(All("kappa", Real, All("t", Real,
            ImpliesClaim(And(Less(D(1), k),
                new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, t)),
                Less(D(0), Call("powerDifference", k, t))))));
    }

    private static Formula DerivativeClaim()
    {
        var k = F.Id("kappa");
        var t = F.Id("t");
        var d = new Formula.Fraction(Multiply(k,
            Subtract(Pow(Add(D(1), t), Subtract(k, D(1))), Pow(t, Subtract(k, D(1))))),
            Call("powerDifference", k, t));
        return Disp(All("kappa", Real, All("t", Real,
            ImpliesClaim(And(Less(D(1), k), Less(D(0), t)),
                Call("HasDerivAt", Call("logPowerDifference", k), d, t)))));
    }

    private static Formula CurvatureClaim()
    {
        var k = F.Id("kappa");
        var t = F.Id("t");
        var c = Call("powerDifference", k);
        var dc = Call("deriv", c, t);
        var ddc = Call("deriv", Call("deriv", c), t);
        var d = Subtract(Pow(Add(D(1), t), Subtract(k, D(1))), Pow(t, Subtract(k, D(1))));
        var curvature = Subtract(Pow(dc, D(2)), Multiply(Call("powerDifference", k, t), ddc));
        var result = Add(Multiply(k, Pow(d, D(2))),
            Multiply(Multiply(k, Subtract(k, D(1))),
                Pow(Multiply(t, Add(D(1), t)), Subtract(k, D(2)))));
        return Disp(All("kappa", Real, All("t", Real,
            ImpliesClaim(Less(D(0), t), Equal(curvature, result)))));
    }

    private static Formula ConcavityClaim()
    {
        var k = F.Id("kappa");
        var b = Call("logPowerDifference", k);
        return Disp(All("kappa", Real, ImpliesClaim(Less(D(1), k),
            And(Call("StrictConcaveOn", Real, Call("Ioi", D(0)), b),
                And(Call("ConcaveOn", Real, Call("Ici", D(0)), b),
                    Equal(Call("logPowerDifference", k, D(0)), D(0)))))));
    }
}
