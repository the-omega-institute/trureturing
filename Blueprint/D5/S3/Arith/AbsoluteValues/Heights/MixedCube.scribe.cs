using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class MixedCubeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed cube satisfies the central-slice volume bound.",
        H("Mixed Cube"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-cube"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/MixedCube.hasSliceBound_mixedCube"),
            H("Mixed Cube"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The mixed cube satisfies the central-slice volume bound."))),
            DescribeRole.Theorem))));
}
