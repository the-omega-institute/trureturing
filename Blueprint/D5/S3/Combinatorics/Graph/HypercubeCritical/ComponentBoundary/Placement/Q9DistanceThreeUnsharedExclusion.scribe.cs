using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceThreeUnsharedExclusionDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceThreeUnsharedExclusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The omitted-edge budget excludes the all-unshared minimum-distance-three case.",
        H("Exclusion of unshared minimum-distance-three contacts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-unshared-distance-three"),
                DeclarationHandle.Create(Owner + "no_unshared_distance_three"),
                H("No unshared minimum-distance-three configuration"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a 258-vertex induced subcubic restriction, take two closed balanced cubic "
                    + "supports of size at least 48 that are mutually separated by at least three. A "
                    + "distance-three contact with all distance-three pairs using disjoint occupied "
                    + "directions would force at least 104 edges inside each exterior and at least 162 "
                    + "edges between the two exteriors. These disjoint exteriors lie in the complement, "
                    + "which would contain at least 370 edges against its cap of 369. This excludes one "
                    + "branch of Hong–Wu–Xia Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ComplementBoundaryBudget")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeActiveBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeCrossingCount"))
        ]));
}
