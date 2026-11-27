using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RankColouredTetrahedronDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport of the tetrahedral certificate",
        H("Transport of the tetrahedral certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("rankcolouredtetrahedron-result"),
            DeclarationHandle.Create("D5/S3/Topology/RankColouredTetrahedron.extra_component_support"),
            H("Transport of the tetrahedral certificate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("A proper four-rank colouring transports the fixed tetrahedral certificate through the third subdivision. Adjacency in an extra component preserves the old edge of the opposite colour."))),
            DescribeRole.Theorem))));
}
