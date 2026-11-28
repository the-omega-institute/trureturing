using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class GeometricGraphTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contiguity from a geometric graph nullhomotopy",
        H("Contiguity from a geometric graph nullhomotopy"),
        Blocks(Describe.Lean(
            DescribeId.Create("geometricgraphtermination-result"),
            DeclarationHandle.Create("D5/S3/Topology/GeometricGraphTermination.realized_graph_map_contracts"),
            H("Contiguity from a geometric graph nullhomotopy"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Suppose the affine realization of a finite simplicial graph map is nullhomotopic. At every sufficiently large ordinary source subdivision depth, composing the map with any choice of vertex in each original support gives a contiguity contraction in the fixed target. Open stars of the target supply a uniform Lebesgue number on the homotopy cylinder."))),
            DescribeRole.Theorem))));
}
