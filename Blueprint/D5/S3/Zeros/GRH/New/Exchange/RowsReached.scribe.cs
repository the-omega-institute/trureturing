using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class RowsReachedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rows Reached", H("Rows Reached"),
        Blocks(
            Paragraph(Text("Descent chain is the transpose of the lift chain, hence onto. Form orthogonal to restrictions of explicit deep level from rank one more vanishes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/RowsReached.eq_zero_of_orthogonal_gridLevelForms"),
                H("eq_zero_of_orthogonal_gridLevelForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("There is a real point g of U(Z_{0,0}) such that a form y of level g₀g₁ on Y₀ vanishes if it is orthogonal to x ↦ φ((x ⊕ 1)g) for all forms φ of principal level Data.gridLevelGen on Z_{0,0} = Y₀ ⊕ ⟨1⟩.")))))));
}
