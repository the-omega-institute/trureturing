using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class GoldenApproximationConstantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci approximants attain the reciprocal square-root-five scaled-error limit.",
        H("Golden Fibonacci Approximation Constant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-fibonacci-scaled-approximation-limit"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/GoldenApproximationConstant."
                    + "golden_fibonacci_approximation_constant_tendsto"),
                H("Scaled Fibonacci approximation errors tend to one over square root five"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Grp(F.Id("F"), Underscore, F.Id("n")), Caret, Grp(D(2)), Sp,
                    Lvert, Varphi, Sp, Minus, Sp,
                    Frac,
                    Grp(F.Id("F"), Underscore,
                        Grp(F.Id("n"), Plus, D(1))),
                    Grp(F.Id("F"), Underscore, F.Id("n")),
                    Rvert, Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(Sqrt, Grp(D(5))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the consecutive Fibonacci approximant F_(n+1)/F_n, multiply the "
                        + "absolute golden-ratio error by the square of its denominator. Once "
                        + "F_n is positive, clearing that denominator identifies this expression "
                        + "with the existing scaled Fibonacci residual score. Its established "
                        + "limit therefore gives exactly 1/sqrt(5).")),
                    Paragraph(Text(
                        "This closes only the asymptotic constant along the Fibonacci convergents. "
                        + "Global optimality, the first two levels of the approximation spectrum, "
                        + "and the semantic uniqueness claim remain unresolved."))),
                DescribeRole.Theorem))));
}
