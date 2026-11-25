using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class GeneralContactOrderCoverageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/GeneralContactOrderCoverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Higher-contact covers of coordinate orders",
        H("Higher-contact covers of coordinate orders"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("higher-opposing-contact"),
                DeclarationHandle.Create(Module + ".exists_signed_higher_contact"),
                H("Opposing contacts of higher coordinate rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose geometric weights in any coordinate order and a largest nonzero kernel coefficient. The signed contribution on every incident empty row must be canceled by an opposing term of strictly higher rank, since the sum of all lower-rank terms is too small."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-contact-order-cover"),
                DeclarationHandle.Create(Module + ".factorial_le_sum_card_cubeOrders"),
                H("Coordinate permutations cover the columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A column covers an order when every empty axis has a higher-ranked neighbor in the local double-flip graph. Counting the covering union gives a factorial bound for arbitrary row multiplicities. Relabeling coordinates acts by permutation on the order sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-higher-contact-order-cover"),
                DeclarationHandle.Create(Module + ".exists_two_components_with_higherContact_orderCoverage"),
                H("Actual two-component necessary condition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each dominant axis of a 258-vertex subcubic support, each of the two selected components has a fixed projected parity and must pass the order-cover bound 40320. Full parity chooses a representative of each pair. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary"))]));
}
