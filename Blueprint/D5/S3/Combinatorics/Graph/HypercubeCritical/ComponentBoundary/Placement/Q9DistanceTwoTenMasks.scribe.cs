using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceTwoTenMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In any 258-vertex subcubic induced candidate, the actual saturated pair realizes at least ten masks on each parity for which a distance-two contact occurs.",
        H("Ten masks at a distance-two contact"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-actual-pair-with-ten-masks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks.exists_actual_pair_with_ten_masks"),
                H("Ten masks at a distance-two contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distance-three and distance-four exclusions leave an actual component pair at distance two. Weighted saturation forces at least three partners at each active axis. At nine masks, the five-axis family is a complete graph with one missing edge and the six-axis family is complete bipartite. The rooted group action and the six-axis rectangle contradiction exclude these alternatives, raising the lower bound from nine masks to ten. This is a restriction on candidates in Hong, Wu and Xia's Problem 2 (arXiv:2610.09483)."))),
                DescribeRole.Theorem)),
        []));
}
