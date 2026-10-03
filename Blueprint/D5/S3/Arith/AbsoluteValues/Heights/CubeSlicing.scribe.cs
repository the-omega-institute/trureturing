using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class CubeSlicingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gaussian slice bound gives central sections of a convex symmetric set volume at least one.",
        H("Cube Slicing"),
        Blocks(Describe.Lean(
            DescribeId.Create("cube-slicing"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/CubeSlicing.one_le_volume_subtype_mem"),
            H("Cube Slicing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A Gaussian slice bound gives central sections of a convex symmetric set volume at least one."))),
            DescribeRole.Theorem))));
}
