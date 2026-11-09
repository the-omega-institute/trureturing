using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CentredCorrelationSummationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centred prime correlations satisfy uniform polynomial logarithmic BV weights.",
        H("Centred weighted correlations"),
        Blocks(
            Paragraph(Text(
                "Assume the strong Hardy–Littlewood correlation estimate for up to four "
                + "distinct positive shifts and an abstract singular series whose empty value is one. "
                + "The centred singular series is its alternating subset transform. "
                + "Weights may jump at integer sampling points.")),
            Describe.Lean(
                DescribeId.Create("centred-polynomial-log-correlation"),
                DeclarationHandle.Create(Prefix + "centred_polynomial_log_correlation"),
                H("Polynomial logarithmic weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a real polynomial p. The sum over N less than n at most 2N of "
                    + "w(n/N) p(log n) times the centred product for D differs from the centred "
                    + "singular series times the integral of w(x/N) p(log x) by at most "
                    + "C B N to the power one half plus epsilon times (1+log N) to the degree of p. "
                    + "The constant is chosen before D and before any compactly supported BV weight "
                    + "whose supremum bound plus variation is at most B. Subtracting two real-cut "
                    + "partial sums supplies the dyadic discrepancy; finite BV summation controls "
                    + "the weight without a continuity assumption."))),
                DescribeRole.Theorem))));
}
