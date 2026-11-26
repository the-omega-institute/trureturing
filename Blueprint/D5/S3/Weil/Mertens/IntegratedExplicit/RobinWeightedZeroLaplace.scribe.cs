using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinWeightedZeroLaplaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Laplace resolvents for zeta zeros.",
        H("Weighted Laplace resolvents for zeta zeros"),
        Blocks(
            Paragraph(Text("The positive Laplace mixture represents the inverse-log weight and exchanges the two absolutely integrable variables. Each occurrence uses its actual coefficient and zero from the integrated explicit formula.")),
            Describe.Lean(DescribeId.Create("mode-tail-resolvent"), DeclarationHandle.Create(Prefix + "modeTail_resolvent"),
                H("One-mode resolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real j at least 1, every complex mode with real part below 1 and every positive lower endpoint, the weighted tail is the integral of its resolvent kernel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occurrence-integral"), DeclarationHandle.Create(Prefix + "weightedZeroContribution_eq_integral_deriv"),
                H("Derivative integral"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The contribution is the weighted integral of the derivative of the integrated mode."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixture"), DeclarationHandle.Create(Prefix + "weightedZeroContribution_eq_mixture"),
                H("Weighted resolvent mixture"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed zero contribution factors into its coefficient, its exponential at the lower endpoint and the resolvent mixture."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("summability"), DeclarationHandle.Create(Prefix + "actualWeightedZeroContribution_summable"),
                H("Occurrence summability"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weighted series indexed by all actual occurrences converges absolutely without a line hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unconditional-bound"), DeclarationHandle.Create(Prefix + "actualWeightedZeroSum_norm_le"),
                H("Unconditional spectral bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The norm of the sum is bounded by the sum of the occurrencewise exponential majorants."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("line-bound"), DeclarationHandle.Create(Prefix + "actualWeightedZeroSum_norm_le_of_line"),
                H("First Li mass bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every actual occurrence lies on the critical line, the coefficient norms sum to the exact first Li mass."))), DescribeRole.Theorem)
        )));
}
