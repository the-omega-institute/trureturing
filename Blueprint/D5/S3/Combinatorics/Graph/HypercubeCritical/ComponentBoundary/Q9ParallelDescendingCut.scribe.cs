using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ParallelDescendingCutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Height cuts and parallel descending edges",
        H("Height cuts and parallel descending edges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-height-cut-count"),
                DeclarationHandle.Create(Module + ".cut_card_heightSublevel"),
                H("Cubic degree balance determines the height cut size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A height sublevel keeps all ascending edges and counts only descending edges crossing its boundary. Internal incidences cancel between the two parity classes, so the cut size is three times their difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-parallel-minority-pairs"),
                DeclarationHandle.Create(Module + ".not_three_minority_pairs_one_axis"),
                H("Three minority pairs cannot lie along the sole mixed axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translation by the axis parity choices makes the three minority pairs parallel descending edges. They would form a three-edge cut, whereas balance forces a singleton side and thus a shared endpoint. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut"))]));
}
