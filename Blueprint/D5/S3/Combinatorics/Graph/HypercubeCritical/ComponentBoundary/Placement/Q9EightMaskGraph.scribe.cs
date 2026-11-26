using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9EightMaskGraphDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9EightMaskGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A minimum-degree-three graph with eight edges is complete on five vertices with two disjoint edges removed.",
        H("The structure of an eight-edge graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eight-edge-family-eq-delete-two"),
                DeclarationHandle.Create(Owner + "eight_edge_family_eq_delete_two"),
                H("Eight edges force five vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree sum bounds the support by five vertices. Eight edges require all five. "
                    + "Deleting two incident edges would give their common endpoint degree two, "
                    + "so the deleted pair is a matching."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "MinimumContactDisplacementCount"))
        ]));
}
