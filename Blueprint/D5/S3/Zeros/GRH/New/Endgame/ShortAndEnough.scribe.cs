using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class ShortAndEnoughDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short And Enough", H("Short And Enough"),
        Blocks(
            Paragraph(Text("Theorem A (Data.short_forms: projected Poincaré series of integral forms have small lifts and small index), Theorem B (Data.enough_forms: few translates nearly span), the remainder as prime sums. N itself is Data.N (New.Seesaw.IndexTypes).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/ShortAndEnough.enough_forms"),
                H("enough_forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Enough forms: columns and rows are non-zero, and for some set t ⊂ 𝖦 with #t·dim(columns) ≤ 5D log(1 + b²), D = dim(rows), the images of the maps Data.projectedPoincare s, s ∈ t, span dimension at least (1 − 4/b²)D.")))))));
}
