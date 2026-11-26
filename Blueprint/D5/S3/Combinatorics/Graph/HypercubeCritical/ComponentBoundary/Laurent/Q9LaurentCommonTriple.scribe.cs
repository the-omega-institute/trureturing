using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentCommonTripleDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentCommonTriple.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common direction triple gives threefold fibers and a descended integer height.",
        H("Projecting away a common direction triple"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-laurent-three-point-fiber"),
                DeclarationHandle.Create(Owner + "exists_star_over_projection"),
                H("Every occupied projection fiber is a single three-leaf star"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If each selected vertex has a unique neighbor of the common direction type, two such centers in the same fiber would have disjoint sets of three leaves. A parity half of a three-cube has four vertices, so a nonempty fiber consists of the leaves of one center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-laurent-height-descends"),
                DeclarationHandle.Create(Owner + "exponent_eq_outside"),
                H("The exponent on the six remaining axes is constant on each fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two vertices in the same fiber share the direction-triple center. The Laurent two-step gain has support in the removed triple, so the other six height coordinates are equal. The Laurent direction partition gives the required unique neighbor whenever the common triple occurs at every selected vertex."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentGainPartition"))]));
}
