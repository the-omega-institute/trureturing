using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtHalfPlaneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Mellin transform of the complete Mangoldt remainder",
        H("Absolute convergence in the open right half-plane"),
        Blocks(
            Describe.Lean(DescribeId.Create("first-exponential-moment-integrable"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane."
                    + "first_moment_integrable"),
                H("Absolute integrability of the first exponential moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every complex s with Re(s)>1, the function y exp((1-s)y) "
                    + "is absolutely integrable over the positive real half-axis. "
                    + "Its norm is y exp(-(Re(s)-1)y), with a strictly positive decay rate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-exponential-moment"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane."
                    + "first_moment"),
                H("The exact first exponential moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Re(s)>1 the integral of y exp((1-s)y) over y>0 is 1/(s-1)^2. "
                    + "The primitive is exp((1-s)y)(y/(1-s)-1/(1-s)^2); "
                    + "its upper endpoint tends to zero by exponential decay. "
                    + "This supplies the logarithmic correction here and the first moment "
                    + "of the Dirichlet parity correction after replacing s by s+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("arithmetic-mellin-transform"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane."
                + "u_laplace_half_plane"),
            H("Transform of the inclusive integrated prime sum"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write x = exp(y). The measure x⁻¹ dx becomes dy, so the Mellin "
                    + "transform of U on x > 1 is the Laplace transform of U(exp(y)) on y > 0. "
                    + "Re(s)>1 makes the arithmetic series absolutely convergent.")),
                Paragraph(Text(
                    "Fix σ = Re(s). Each nonnegative Mangoldt ramp is multiplied by exp(−sy). "
                    + "Its norm equals the ramp multiplied by exp(−σy). Its norm integral thus "
                    + "equals the real part of the individual ramp transform at σ. The convergent "
                    + "von Mangoldt Dirichlet series at σ makes these norm integrals summable. "
                    + "Tonelli gives absolute integrability of the sum, and its complex integral "
                    + "can be computed term by term, yielding (−ζ′(s)/ζ(s))/(s(s−1)).")),
                Paragraph(Text(
                    "The logarithmic correction integrates to −1/(s−1)² and the linear "
                    + "correction integrates to (1+γ)/(s−1). In the first moment the boundary "
                    + "term at infinity vanishes because y exp(−(σ−1)y) tends to zero."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var s = F.Id("s");
        var y = F.Id("y");
        var one = F.D(1);
        var sMinusOne = Subtract(s, one);
        var halfLine = Apply("Ioi", F.D(0));
        var body = Multiply(Apply("exp", new Formula.Negate(Multiply(s, y))),
            Apply("U", Apply("exp", y)));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, y, F.Sp, F.Mapsto, F.Sp, body, F.Close);
        var integral = F.Seq(F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(F.Infty),
            F.Sp, body, F.Sp, F.Id("d"), y);
        var logDerivative = new Formula.Fraction(new Formula.Negate(
            new Formula.Apply(F.Seq(F.Zeta, F.Apos), [s])), new Formula.Apply(F.Zeta, [s]));
        var value = Add(Subtract(new Formula.Fraction(logDerivative, Multiply(s, sMinusOne)),
            new Formula.Fraction(one, F.Seq(F.Open, sMinusOne, F.Close, F.Caret, F.Grp(F.D(2))))),
            new Formula.Fraction(Add(one, F.GammaLower), sMinusOne));
        var result = new Formula.Logic(Apply("IntegrableOn", function, halfLine),
            FormulaLogicOperator.And,
            new Formula.Relation(integral, FormulaRelationOperator.Equal, value));
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"),
            F.Seq(F.Mathbb, F.Grp(F.Id("C"))),
            new Formula.Logic(new Formula.Relation(one, FormulaRelationOperator.LessThan,
                Apply("Re", s)),
                FormulaLogicOperator.Implies, result)));
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
