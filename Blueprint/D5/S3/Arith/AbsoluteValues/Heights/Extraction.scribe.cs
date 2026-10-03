using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class ExtractionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extract a linearly independent subfamily with controlled index positions across fields.",
        H("Extraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("extraction"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Extraction.exists_linearIndependent_comp_finrank_mul"),
            H("Extraction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Extract a linearly independent subfamily with controlled index positions across fields."))),
            DescribeRole.Theorem))));
}
