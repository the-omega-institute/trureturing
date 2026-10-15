using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class LeechFrameRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integer Gram rows factor the literal hyperbolic frame calculation.",
        H("Literal Leech Gram Rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leechframerows"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows.literalGramRows_eq"),
                H("Literal Leech Gram Rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The rows of R are the twenty-four literal integral binary frame vectors. The matrix literalGramRows is exactly R times the original ExplicitLeechBasis.gramMatrix. Thus the pairing of two frame rows is the dot product of a literal Gram row with the other integral vector.")),
                    Paragraph(Text("This integer factorization preserves the full original quadratic and polar calculation. It neither substitutes an ambient-coordinate form nor enumerates the 2^24 charges. The resulting entries are used to certify the original hyperbolic basis and its native representation action."))),
                DescribeRole.Theorem))));
}
