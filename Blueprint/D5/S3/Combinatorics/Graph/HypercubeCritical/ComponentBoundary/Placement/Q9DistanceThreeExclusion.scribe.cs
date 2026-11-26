using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceThreeExclusionDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceThreeExclusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a hypothetical subcubic 258-vertex restriction of the nine-cube, the two balanced cubic components have minimum distance two.",
        H("Reduce the nine-cube problem to distance two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-minimum-distance-three"),
                DeclarationHandle.Create(Owner + "no_minimum_distance_three"),
                H("Minimum distance three is excluded"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A shared occupied direction is impossible by the normalized finite refutations. The "
                    + "remaining distance-three pairs have disjoint occupied directions. The exterior edge "
                    + "budget excludes that configuration in the proposed restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-two-balanced-components-at-distance-two"),
                DeclarationHandle.Create(Owner + "exists_two_balanced_components_at_distance_two"),
                H("The two balanced components have minimum distance two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Huang's signing extracts two distinct balanced induced cubic components from a "
                    + "subcubic 258-vertex candidate for Hong–Wu–Xia Problem 2. Their minimum distance "
                    + "belongs to two, three or four. The two exclusion proofs leave distance two. "
                    + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeUnsharedExclusion")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactGeometryReplay")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceFourExclusion"))
        ]));
}
