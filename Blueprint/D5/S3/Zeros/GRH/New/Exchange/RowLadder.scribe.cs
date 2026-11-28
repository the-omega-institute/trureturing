using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class RowLadderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row Ladder", H("Row Ladder"),
        Blocks(
            Paragraph(Text("The one-square lemma applied to a grid square, constant costing one square.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/RowLadder.descent_past_gridPathMap"),
                H("descent_past_gridPathMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A descent moves past a lifts. For a ≤ b < m there are κ and c(ϑ) ≠ 0 costing a squares such that, if each edge of w avoids grid z or is (i, b) → (i+1, b) with i ≥ a, every tidy Λ of order n has a tidy Φ of order n + 2a with Λ(path to (a, b)) = (κ/c(ϑ))·Φ(path to (a, b+1), then descent), under linear functionals reading only w.")))))));
}
