using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class RobinFixedExponentWindowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/Analytic/RobinFixedExponentWindows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed mass comparison from a fixed Mangoldt exponent",
        H("Logarithmic saving under a cofinal one-sided bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("fixed-exponent-signed-mass-comparison"),
                DeclarationHandle.Create(Module + "signed_mass_comparison_of_frequently_window_bound"),
                H("The normalized weighted and unweighted masses"),
                StatementSource.FromAuthor(Comparison()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix 0 < κ < 1/2 and b > 1. Assume that a single coefficient "
                        + "bounds the positive side of the integrated Mangoldt remainder by "
                        + "C₀ x^(1/2+κ) throughout arbitrarily late windows [Y,Y^b].")),
                    Paragraph(Text("The cofinal bound excludes every zero with real part above "
                        + "1/2+κ. The actual terminal defect therefore admits the bound "
                        + "K x^(κ−1/2)/log x for x≥exp(1).")),
                    Paragraph(Text("For either sign, let Mw and Mq be the weighted and ordinary "
                        + "tail masses on [A,B], exp(1)≤A≤B, both normalized by 1/sqrt(t). "
                        + "The weighted tail carries the inverse logarithmic weight. "
                        + "Taking positive parts preserves the defect bound. Replacing "
                        + "log(t) in the denominator by log(A) gives the displayed integral comparison."))),
                DescribeRole.Theorem))));

    private static Formula Comparison()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var kappa = F.Id("kappa");
        var log = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [a]);
        var difference = Subtract(Seq(b, Caret, Grp(kappa)), Seq(a, Caret, Grp(kappa)));
        var scale = new Formula.Fraction(F.Id("K"), Multiply(kappa, log));
        var massDifference = Subtract(F.Id("Mw"), F.Id("Mq"));
        return Disp(new Formula.Relation(Seq(Bar, massDifference, Bar),
            FormulaRelationOperator.LessThanOrEqual, Multiply(scale, Seq(Open, difference, Close))));
    }
}
