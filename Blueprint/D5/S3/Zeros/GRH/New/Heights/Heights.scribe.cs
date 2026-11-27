using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Heights;

internal sealed class HeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Heights", H("Heights"),
        Blocks(
            Paragraph(Text("Heights of families indexed by ℓ-adic embeddings: additivity and product formula.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Heights/Heights.nonneg"),
                H("nonneg"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Product formula: if the constant family 1 has height at most c, then c ≥ 0.")))))));
}
