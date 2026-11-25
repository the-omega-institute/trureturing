using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SmallSpectrumDichotomyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallSpectrumDichotomy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Component orders under the paired-fibre alternative",
        H("Component orders under the paired-fibre alternative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-parity-of-order-seventy-two"),
                DeclarationHandle.Create(Module + ".pure_parity_of_order_seventy_two"),
                H("Order 72 forces one projected parity on every axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A full eight-star supplies pairs in both parities along each other axis. At order 72 this would force all axes to carry full stars, contradicting the packing bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-ne-eighty-four"),
                DeclarationHandle.Create(Module + ".order_ne_eighty_four"),
                H("The order-84 split violates parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divisibility forces a thirteen-to-one split wherever one parity contains twelve or more double fibres. Star packing and the minority counts force the split on all nine axes, contradicting the descending-edge congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ninety-le-of-not-seventy-two"),
                DeclarationHandle.Create(Module + ".ninety_le_of_not_seventy_two"),
                H("The first remaining order is at least 90"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given the local eight-star or twelve-pair alternative on every axis and exclusion of the adjacent-layer order-72 case, the projected parity counts and the congruence exclude the intervening orders. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity"))]));
}
