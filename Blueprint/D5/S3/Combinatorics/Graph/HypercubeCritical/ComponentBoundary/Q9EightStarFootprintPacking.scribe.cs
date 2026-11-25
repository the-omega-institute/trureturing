using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightStarFootprintPackingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Packing eight-stars across coordinate axes",
        H("Packing eight-stars across coordinate axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eight-star-disjoint-footprints"),
                DeclarationHandle.Create(Module + ".starFootprint_disjoint"),
                H("Disjoint thirty-two-vertex footprints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A star uses sixteen lifted spokes and sixteen cross-corner vertices. A center of another axis cannot approach within three transverse flips. Consequently the second spoke set avoids the first footprint. A shared cross corner would have four selected neighbors, violating cubicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-star-axis-packing"),
                DeclarationHandle.Create(Module + ".thirty_two_mul_card_le_of_eight_stars"),
                H("Counting distinct star directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing pairwise disjoint footprints gives 32 vertices per distinct star direction. In a component of order at most 126, at most three axes can have full eight-stars. Nine star directions are impossible in any cubic subset of a hypothetical 258-set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-star-transverse-pair-parity"),
                DeclarationHandle.Create(Module + ".doubleFibres_ge_two_of_eightStar"),
                H("Both transverse parity classes contain pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four cross edges in each other direction split two per axial layer. This forces at least two pairs of each projected parity, linking local cube geometry with the arithmetic of weighted boundary supports. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound"))]));
}
