using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SignedSeriesFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fibres of the Signed Golden Series.",
        H("The Fibres of the Signed Golden Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signedseriesfibres-signed-series-fibres"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SignedSeriesFibres.signed_series_fibres"),
                H("Two streams at each seam"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write legal infinite digits as blocks zero and one followed by zero. "
                    + "For every finite block word w, including the empty word, its affine image "
                    + "of minus alpha cubed has exactly two distinct streams: w followed by the "
                    + "zero block and the upper alternating stream, and w followed by the one-zero "
                    + "block and that same alternating stream. Different words give different "
                    + "seam values. Every other value in the closed interval from minus alpha "
                    + "to alpha squared has exactly one stream."))),
                DescribeRole.Theorem))));
}
