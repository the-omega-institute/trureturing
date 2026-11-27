using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FourteenMaskNineAxisExclusionDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourteen masks cannot use all nine axes.",
        H("Fourteen masks cannot use all nine axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-fourteen-masks-on-nine-axes"),
                DeclarationHandle.Create(Placement + "Q9FourteenMaskNineAxisExclusion.no_fourteen_masks_on_nine_axes"),
                H("Fourteen masks cannot use all nine axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Hong, Wu and Xia ask whether f2(Q9) equals three in Problem 2 of Graph Sensitivity of Cartesian Products with Matched Bridges (https://arxiv.org/html/2610.09483v1#Thmproblem2). A distance-two contact pair of saturated components gives a graph on the active axes. Coordinate translations force the additional common-neighbor condition at every cubic edge. The graph counting obstruction then excludes the fourteen-mask case on nine axes. Other contact graphs remain possible under this theorem."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9FourteenMaskGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ContactGraphTriangles")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SquareMaskGraph"))]));
}
