using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RankCuts;

internal sealed class RankedBipartiteCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Use degree capacities to bound the charge in an ordered bipartite graph.",
        H("Capacity bounds for ranked bipartite graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-sided-capacity-by-rank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.two_sided_rank_capacity"),
                H("Two-sided capacity at each rank"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("CapacityDeficit", F.Id("r")),
                    FormulaRelationOperator.LessThanOrEqual,
                    Call("DiagonalMultiplicity", F.Id("r"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use two copies of a finite vertex set ranked by natural numbers "
                        + "and natural-valued edge multiplicities. Fix an exceptional vertex t of "
                        + "rank above r. Ordinary positive rows are diagonal or go up in rank. Each "
                        + "ordinary row and column has total multiplicity between one and k.")),
                    Paragraph(Text("The lower deficit subtracts k times the number of rows below r and "
                        + "the exceptional row's actual inflow to the columns at or below r from the "
                        + "number of those columns. The upper deficit uses the ordinary rows at or above "
                        + "r, the number of ordinary columns strictly above r multiplied by k, and the "
                        + "actual outflow from ordinary rows of rank at least r to the exceptional column. "
                        + "Both differences are truncated at "
                        + "zero. Their maximum is CapacityDeficit(r), and DiagonalMultiplicity(r) sums "
                        + "the diagonal at rank r."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("odd-rank-diagonal-capacity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.paid_edges_ge_rank_capacity"),
            H("Summed capacity deficits bound the odd-rank edge charge"),
            StatementSource.FromAuthor(Disp(new Formula.Relation(
                Call("CapacityDeficitSum", F.Id("R")),
                FormulaRelationOperator.LessThanOrEqual,
                Call("OddEdgeCharge", F.Id("e"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use two copies of a finite vertex set with natural-number ranks and "
                    + "natural edge multiplicities e. Fix a vertex t. Each positive entry from "
                    + "an ordinary row is diagonal or goes to a strictly higher rank. Every ordinary "
                    + "row and column has total multiplicity between one and k.")),
                Paragraph(Text("Let R be a finite set of odd ranks below the rank of t. At a rank r in R, "
                    + "subtract k times the number of vertices strictly below r and the actual weight "
                    + "from row t into columns at or below r from the number of vertices at or below r. "
                    + "Also subtract k times the number of ordinary vertices strictly above r and the "
                    + "actual weight from ordinary rows at or above r into column t from the number "
                    + "of ordinary vertices at or above r. Take the maximum of zero and these two "
                    + "differences. CapacityDeficitSum sums the resulting value over R.")),
                Paragraph(Text("OddEdgeCharge sums e over edges from ordinary odd-rank rows to "
                    + "odd-rank columns. In the first count, positive entries reaching the lower "
                    + "prefix from ordinary rows at or above its boundary can only use its diagonal. "
                    + "In the second count, positive entries leaving the upper suffix for columns "
                    + "at or below its boundary also use its diagonal. Each layer has a disjoint "
                    + "set of diagonal entries. Their contributions therefore sum within the charge."))),
            DescribeRole.Theorem))));
}
