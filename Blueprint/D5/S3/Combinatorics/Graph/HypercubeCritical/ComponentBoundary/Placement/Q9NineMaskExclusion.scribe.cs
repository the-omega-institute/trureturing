using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9NineMaskExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five active coordinates give the six normalized orbits. Six active coordinates give the complete bipartite contact graph and its two aligned parity rectangles. Both branches are excluded.",
        H("Nine contacts are impossible in the saturated pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-nine-masks-in-actual-pair"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NineMaskExclusion.no_nine_masks_in_actual_pair"),
                H("Nine contacts are impossible in the saturated pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Five active coordinates give the six normalized orbits. Six active coordinates give the complete bipartite contact graph and its two aligned parity rectangles. Both branches are excluded."))),
                DescribeRole.Theorem)),
        []));
}
