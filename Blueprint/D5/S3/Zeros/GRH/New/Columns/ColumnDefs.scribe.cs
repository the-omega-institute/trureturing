using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class ColumnDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Column Defs", H("Column Defs"),
        Blocks(
            Paragraph(Text("the primes of E dividing π; the levels on the spaces X_j; columns, that is, algebraic forms on X_0 (not the columns of a Young diagram, nor IsColumn); branching and restriction from X_m to Y_m.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/ColumnDefs.le_branchExp"),
                H("le_branchExp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At every infinite place τ, the exponent n_τ (Data.branchExp) is at least κ_τ(1) − 2b, where κ_τ(1) is the number of columns of height one at τ.")))))));
}
