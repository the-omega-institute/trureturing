using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Descent;

internal sealed class TestCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Test Cover", H("Test Cover"),
        Blocks(
            Paragraph(Text("One test covers all points; dévissage from representables to affinely covered functors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/TestCover.hasFlatBaseChange"),
                H("hasFlatBaseChange"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ι from C to A-algebras be fully faithful, and suppose each A-algebra B with a point in some ι(c) has one point through which all its points factor. If Y is affinely covered (IsAffinelyCovered), then ℤ[Y] has flat base change.")))))));
}
