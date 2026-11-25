using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactOrderCoverageDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactOrderCoverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate permutation coverage by integer exponent gains",
        H("Coordinate permutation coverage by integer exponent gains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-permutation-cover-count"),
                DeclarationHandle.Create(Module + ".card_perm_le_sum_card_localOrders"),
                H("The total local cover contains at least all coordinate permutations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The collection of all local order sets covers the coordinate "
                    + "permutations. The union bound compares its cardinality with the "
                    + "sum of the local cardinalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-integer-gains-cover-orders"),
                DeclarationHandle.Create(Module + ".exists_mem_localOrders"),
                H("Each coordinate order occurs in at least one local maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Maximize the scalar product of an integer exponent potential with "
                    + "the ranks of a coordinate permutation over a finite nonempty set of "
                    + "columns. Each available step adds one source axis and subtracts its "
                    + "target axis. Maximality and distinct ranks force each target to have "
                    + "larger rank than all sources in its block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-eight-axis-weighted-coverage"),
                DeclarationHandle.Create(Module + ".weighted_order_coverage"),
                H("Four exponent steps give the eight-axis weighted covering inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Independent permutations within disjoint blocks act on coordinate "
                        + "orders and carry each fibre of the block maxima bijectively to "
                        + "every other fibre. With four source axes and disjoint blocks "
                        + "of size two or three, "
                        + "the possible products of block sizes are sixteen, twelve and nine. "
                        + "The permutation fibres have respectively 2520, 3360 and 4480 "
                        + "members out of 40320. The union covers all permutations, yielding "
                        + "the bound 144 by the weighted column counts 9, 12 and 16.")),
                    Paragraph(Text(
                        "In the eight transverse coordinates of the paired-fibre analysis "
                        + "for Hong, Wu and Xia's Problem 2, the counts distinguish columns "
                        + "with different numbers of two-source targets. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactTransport"))]));
}
