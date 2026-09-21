using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialPoweredRatioLocalizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/byun2026unimodality");

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
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "poweredRatio(a,l,m,r) = sum(i=0..r, (choose(m,i) a^i)^l) "
                    + "/ sum(i=0..r, (choose(r,i) a^i)^l). Both products, "
                    + "including their weights, are raised to l. This is the "
                    + "sequence in equation (1.4) of the source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-powered-ratio-maximizer-slope"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization.actual_maximizer_slope"),
                H("Every maximizing choice has slope a divided by one plus two a"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every fixed positive real a and positive natural l, any "
                    + "sequence r(m)<=m maximizing poweredRatio over every "
                    + "integer 0<=j<=m has r(m)/m tending to "
                    + "a/(1+2a). A power-mean denominator bound contributes a "
                    + "polynomial factor, which the existing exponential separation "
                    + "absorbs. Ties are allowed, with no uniqueness or unimodality "
                    + "premise. The slope alone does not supply the exact maximum "
                    + "prefactor or any exact peak assertion."))),
                DescribeRole.Theorem))));
}
