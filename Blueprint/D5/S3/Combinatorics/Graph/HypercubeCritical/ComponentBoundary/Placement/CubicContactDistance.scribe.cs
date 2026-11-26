using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class CubicContactDistanceDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Owner = Cube + "ComponentBoundary/Placement/CubicContactDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closest pairs of induced cubic cube supports with Huang balance on one side.",
        H("Five coordinates of agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-closest-pair-five-agreement-axes"),
                DeclarationHandle.Create(Owner + "closest_pair_distance_add_five_le"),
                H("Five agreement axes for a closest pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a closest pair, either endpoint can have neighbors only "
                        + "along axes where the endpoints agree. With at most four agreement "
                        + "axes, the two sets of three neighbor directions share an axis. "
                        + "Flipping that axis at both endpoints preserves distance and agreement. "
                        + "The old and new vertices in the balanced support share only the "
                        + "flipped direction, since another shared direction would complete a "
                        + "coordinate square. Their two sets of three directions therefore "
                        + "require five distinct agreement axes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-actual-components-closest-distance-range"),
                DeclarationHandle.Create(Owner + "exists_two_components_at_distance_two_to_four"),
                H("The closest distances for the nine-cube problem"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A hypothetical 258-point support of induced maximum degree "
                        + "three contains two actual balanced cubic components. A closest pair "
                        + "between them has distance at least two by component separation and "
                        + "at most four by the five agreement axes. This gives the three "
                        + "distance cases in Hong, Wu and Xia’s Problem 2. "
                        + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCubeComponentBoundary")),
         DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCubeGirth")),
         DocumentEdge.Dependency.Create(GidRef.Create(Cube + "TwoBalancedComponents"))]));
}
