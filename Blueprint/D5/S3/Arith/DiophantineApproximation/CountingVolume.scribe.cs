using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class CountingVolumeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The volume of a cube-simplex intersection has an exponential upper bound.",
        H("Counting Volume"),
        Blocks(Describe.Lean(
            DescribeId.Create("counting-volume"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/CountingVolume.cubeSimplexVolume_le_exp_neg"),
            H("Counting Volume"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The volume of a cube-simplex intersection has an exponential upper bound."))),
            DescribeRole.Theorem))));
}
