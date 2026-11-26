using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class TriangleArrowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle Arrows", H("Triangle Arrows"),
        Blocks(
            Paragraph(Text("The lifts and descents of the data form a triangle with two laws.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/TriangleArrows.exists_isTriangle"),
                H("exists_isTriangle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For some descents d, the lifts Data.triLift, the orders Data.triangleOrder, the cost Data.CostsSquares and the embeddings of Data.triBase in the forms at (i, 0) form a triangle IsTriangle of size m; the cost bound and second law are asserted for z false only.")))))));
}
