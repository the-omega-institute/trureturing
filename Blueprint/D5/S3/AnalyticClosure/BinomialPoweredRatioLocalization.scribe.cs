using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialPoweredRatioLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximizers of the ratio of powered binomial sums have a common limiting slope.",
        H("Localization for the Powered-Sum Ratio"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("powered-binomial-sum-ratio"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.poweredRatio"),
                H("The actual ratio of powered sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The denominator sums the l-th powers of choose(r,i) times a^i "
                    + "over the full row r. The numerator uses row m and stops at r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-powered-ratio-maximizer-slope"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.actual_maximizer_slope"),
                H("Every maximizing choice has slope a divided by one plus two a"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real a and positive natural l, any choice "
                    + "of maximizing r between zero and m has r/m tending to "
                    + "a/(1+2a). A power-mean denominator bound contributes a "
                    + "polynomial factor, which the existing exponential separation "
                    + "absorbs. Ties are allowed, with no uniqueness or unimodality premise."))),
                DescribeRole.Theorem))));
}
