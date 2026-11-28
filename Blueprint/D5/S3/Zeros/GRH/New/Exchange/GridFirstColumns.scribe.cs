using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class GridFirstColumnsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grid First Columns", H("Grid First Columns"),
        Blocks(
            Paragraph(Text("Twist-free restriction projected to level g; periods under translation; index ratios.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/GridFirstColumns.exists_isTidy_diagonalPeriodForm_eq"),
                H("exists_isTidy_diagonalPeriodForm_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For some C, every ϑ has a datum Λ, tidy of order 4m on Data.path 0, such that Data.triangleOrder at node (0, m) of V times the period Data.diagonalPeriodForm over U(Y₀) of the descents Data.iotaPlus of Ξ, φ equals C times Data.gridPeriod for Λ.")))))));
}
