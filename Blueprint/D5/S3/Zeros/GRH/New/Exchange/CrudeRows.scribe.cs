using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class CrudeRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crude Rows", H("Crude Rows"),
        Blocks(
            Paragraph(Text("The main result Data.crude_rows. Pairings of twisted chains of all rows are multiples of the end period.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/CrudeRows.crude_rows"),
                H("crude_rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Some nowhere zero c(ϑ) costs 2m² squares (Data.CostsSquares), and the forms of level K(g) on Y₀ are spanned by the y with c(ϑ)/c(1)·ι_ϑ y integral above every l prime to the norms in Q(ϑ) and all conjugates of values of ι₁y of squared norm ≤ exp(x₁²b²).")))))));
}
