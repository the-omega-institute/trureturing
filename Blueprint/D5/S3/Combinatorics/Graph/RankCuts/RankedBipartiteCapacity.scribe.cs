using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RankCuts;

internal sealed class RankedBipartiteCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Use degree capacities to bound the charge in an ordered bipartite graph.",
        H("Capacity bounds for ranked bipartite graphs"),
        Blocks(Describe.Lean(
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
                    + "row and column has total multiplicity between one and k. The t row and t column "
                    + "have total multiplicities at most ka and kb, respectively.")),
                Paragraph(Text("Let R be a finite set of odd ranks below the rank of t. At a rank r in R, "
                    + "subtract k times the number of vertices strictly below r plus ka from the number "
                    + "of vertices at or below r. Also subtract k times the number of ordinary vertices "
                    + "strictly above r plus kb from the number of ordinary vertices at or above r. "
                    + "Take the maximum of zero and these two differences. CapacityDeficitSum sums "
                    + "the resulting value over R.")),
                Paragraph(Text("OddEdgeCharge sums e over edges from ordinary odd-rank rows to "
                    + "odd-rank columns. In the first count, positive entries reaching the lower "
                    + "prefix from ordinary rows at or above its boundary can only use its diagonal. "
                    + "In the second count, positive entries leaving the upper suffix for columns "
                    + "at or below its boundary also use its diagonal. Each layer has a disjoint "
                    + "set of diagonal entries. Their contributions therefore sum within the charge."))),
            DescribeRole.Theorem))));
}
