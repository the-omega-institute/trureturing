using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class RowVolumeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row Volume", H("Row Volume"),
        Blocks(
            Paragraph(Text("Volume of the chain on rows factors into volumes of single lifts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/RowVolume.range_goodLift_le"),
                H("range_goodLift_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 1 ≤ j ≤ m, a subspace N that contains θ_{j,ϑ}^* y for every good form y on U(W_j) with a Hecke eigensystem whose lift lies in the image of the idempotent of one good tuple contains all lifts of good forms (the range of Data.goodLift).")))))));
}
