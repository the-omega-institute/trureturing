using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9ExteriorEdgeLiftCountDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9ExteriorEdgeLiftCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parallel flips force edges inside the exterior of a balanced cubic support.",
        H("Parallel flips of occupied edges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exterior-edges-ge-one-hundred-four"),
                DeclarationHandle.Create(Owner + "exterior_edges_ge_one_hundred_four"),
                H("An exterior with at least 104 edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take a balanced induced cubic support on at least 48 vertices. Suppose at least 45 "
                    + "exterior vertices have exactly two support neighbors and at least two exterior "
                    + "neighbors outside that distinguished set. Each occupied edge admits four parallel "
                    + "flips into the exterior. Even exterior degree bounds the number of lifts of an "
                    + "exterior edge by eight. Every edge incident to the distinguished set has at most two "
                    + "lifts. The hypotheses force at least 90 such edges. Counting the lifts yields the "
                    + "lower bound of 104 exterior edges."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "CubicContactDistance"))
        ]));
}
