using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SquareMaskGraphDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SquareMaskGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forced squares constrain the number and shape of distance-two contact masks.",
        H("The mask graph of a distance-two component pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distance-two-mask-graph-constraints"),
                DeclarationHandle.Create(Owner + "distance_two_mask_graph_constraints"),
                H("Minimum degree and square completion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For separated connected balanced cubic components with universally singular signed defect, the mask graph has minimum degree three and square completion along edges between cubic vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-eleven-masks-on-seven-axes"),
                DeclarationHandle.Create(Owner + "no_eleven_masks_on_seven_axes"),
                H("Seven axes exclude eleven masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eleven edges on seven axes with minimum degree three would leave a unique degree-four vertex. Square completion rules out this graph."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nine-masks-on-six-axes-bipartite"),
                DeclarationHandle.Create(Owner + "nine_masks_on_six_axes_bipartite"),
                H("Nine masks on six axes force K3,3"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nine edges on six axes make the mask graph cubic. Square completion then forces the complete bipartite graph with two three-axis parts."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9EightMaskGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DegreeThreeContactOrbit"))
        ]));
}
