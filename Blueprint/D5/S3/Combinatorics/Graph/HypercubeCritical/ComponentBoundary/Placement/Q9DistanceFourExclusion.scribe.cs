using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceFourExclusionDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceFourExclusion.";
    private const string Problem = "<https://arxiv.org/html/2610.09483v1#Thmproblem2>";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exclusion of minimum distance four between balanced cubic nine-cube supports.",
        H("Simultaneous flips at minimum distance four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-balanced-cubic-no-minimum-distance-four"),
                DeclarationHandle.Create(Owner + "no_distance_four_of_four_separated"),
                H("Minimum distance four is impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix an endpoint in the second support. At distance four, "
                    + "each endpoint has three occupied directions among the five agreeing axes. "
                    + "A common direction flips both endpoints and preserves their displacement. "
                    + "The absence of a square makes the union of directions at the two adjacent "
                    + "vertices in the second support equal to the five agreeing axes. "
                    + "Thus each direction at the fixed endpoint determines at most one contact, "
                    + "giving at most three. Flipping each of the four differing axes reaches an "
                    + "exterior vertex. Evenness gives another occupied neighbor that is again at "
                    + "distance four and agrees with the fixed endpoint on precisely that one of "
                    + "the four original differing axes. This gives four distinct contacts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-actual-components-distance-two-or-three"),
                DeclarationHandle.Create(Owner + "exists_two_components_at_distance_two_or_three"),
                H("The two balanced components have minimum distance two or three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the hypothetical subcubic 258-vertex branch of "
                    + "Hong–Wu–Xia Problem 2, the closest pair of the two extracted balanced cubic "
                    + "components has distance at least two. The five-axis agreement bound gives "
                    + "distance at most four, and the fixed-endpoint argument excludes four. "
                    + Problem))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "CubicContactDistance"))
        ]));
}
