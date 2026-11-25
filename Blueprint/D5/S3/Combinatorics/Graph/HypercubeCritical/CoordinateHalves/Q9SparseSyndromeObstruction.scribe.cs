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
                DescribeId.Create("sparse-syndrome-at-order-72"),
                DeclarationHandle.Create(Module + ".sparse_syndrome_at_order_72"),
                H("A nonempty order-72 sparse syndrome has sixteen sites and a saturated exterior shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two fold equations fix the residual squared norm at 32 when there are twelve dimers and forty-eight singleton sites. The energy bound allows at most sixteen syndrome sites. Below sixteen, the binary adjacency kernel classification leaves the empty word, one shell, and a symmetric difference of two shells. The latter two have a row with more than two syndrome neighbors. At weight sixteen, some nonzero residual site outside the syndrome must have all eight of its neighbors among the rows with two syndrome neighbors. Otherwise the exterior capacity is at most seven, which forces the weight below sixteen.")),
                    Paragraph(Text("The fold is a conditional case in Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
