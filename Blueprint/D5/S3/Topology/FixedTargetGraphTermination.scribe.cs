using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FixedTargetGraphTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite triangle moves on padded paths",
        H("Finite triangle moves on padded paths"),
        Blocks(Describe.Lean(
            DescribeId.Create("simultaneous-padded-comparison"),
            DeclarationHandle.Create(
                "D5/S3/Topology/FixedTargetGraphTermination.simultaneous_padded_comparison"),
            H("A finite family of edge-path comparisons has a common padding length"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "For a finite family of paths related by insertions and deletions across target triangles, choose a bound on every intermediate length. At any interval length above that bound, every admissible pair of endpoint-preserving paddings is connected by a common relative contiguity chain. Moving a repeated vertex frees the slot needed for a triangle insertion."))),
            DescribeRole.Theorem))));
}
