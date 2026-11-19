using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMRadialClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Three Radial Comparisons for Creation Words",
        H("The Three Radial Comparisons for Creation Words"),
        Blocks(Describe.Lean(DescribeId.Create("radial-word-crossings"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialClosure.radial_word_crossings"),
            H("The A, B and D comparisons for four words"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Label each occurrence in the four words by its position. On the common real interval the marked coefficients give the literal Laurent readouts with their original signs. The same physical coefficient then relates the three charts."))),
            DescribeRole.Theorem))));
}
