using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class PrekopaLeindlerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euclidean volume satisfies the Prekopa-Leindler inequality.",
        H("Prekopa Leindler"),
        Blocks(Describe.Lean(
            DescribeId.Create("prekopa-leindler"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/PrekopaLeindler.hasPrekopaLeindler_euclideanSpace"),
            H("Prekopa Leindler"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Euclidean volume satisfies the Prekopa-Leindler inequality."))),
            DescribeRole.Theorem))));
}
