using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9SparseSyndromeObstructionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shell capacity bounds signed lifts of sparse cube syndromes.",
        H("Shell capacity bounds signed lifts of sparse cube syndromes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-syndrome-energy"),
                DeclarationHandle.Create(Module + ".sparse_syndrome_energy"),
                H("The signed lift energy is bounded by the exterior shell capacity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every row has zero or two neighbors in the odd support. Huang’s squared operator identity makes exactly twice the support cardinality of the unit-signed rows nonzero. Each such row needs a correction for divisibility by four. The shell of a corrected site inside the support reaches at most eight rows and costs at least eight units of squared energy. An exterior correction reaches at most the specified shell capacity and costs at least four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-syndrome-empty-at-order-72"),
                DeclarationHandle.Create(Module + ".sparse_syndrome_empty_at_order_72"),
                H("The order-72 fold forces the sparse syndrome to be empty"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two fold equations fix the residual squared norm at 32 when there are twelve dimers and forty-eight singleton sites. The energy bound allows at most sixteen syndrome sites. Below sixteen, the binary adjacency kernel classification leaves the empty word, one shell, and a symmetric difference of two shells. The latter two have a row with more than two syndrome neighbors. At weight sixteen, some nonzero residual site outside the syndrome must have all eight of its neighbors among the rows with two syndrome neighbors. Otherwise the exterior capacity is at most seven, which forces the weight below sixteen.")),
                    Paragraph(Text("Translate that exterior site to the origin. The eight syndrome sites at distance two give a two-regular graph on the coordinate set. At least thirty-two distance-three rows each see one of those sites and need a second neighbor at distance four. This uses the entire allowance of eight more sites and all of their lower neighbors. Two distance-four sites with a common distance-five row also have a common distance-three row. The lower rows each admit just one distance-four site, so each distance-five row adjacent to a syndrome site sees exactly one. This violates the row hypothesis.")),
                    Paragraph(Text("The fold is a conditional case in Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
