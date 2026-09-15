using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SignedSeriesRangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Range of the Signed Golden Series.",
        H("The Range of the Signed Golden Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signedseriesrange-signed-series-range"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SignedSeriesRange.signed_series_range"),
                H("The interval and its endpoint fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let alpha be the reciprocal of the golden ratio. For infinite Boolean digits "
                    + "with no adjacent ones, indexed from low to high, the sum of the digits with "
                    + "coefficients minus alpha squared, alpha cubed, minus alpha to the fourth, "
                    + "and so on has range exactly the closed interval from minus alpha to alpha "
                    + "squared. The lower endpoint is attained only by the alternating stream "
                    + "starting with one, and the upper endpoint only by the alternating stream "
                    + "starting with zero. Every real number outside this interval has empty fibre. "
                    + "Termwise comparison gives the bounds and strictness away from the alternating "
                    + "streams. Repeated inverse branches construct legal digits for every point "
                    + "in the interval, with a remainder tending to zero."))),
                DescribeRole.Theorem))));
}
