using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class FixedNeighborOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact transcript likelihood under one fixed random ordering per vertex.",
        H("Likelihood of complete ordered neighbor replies"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-neighbor-order-likelihood"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/FixedNeighborOrder.fixed_neighbor_order_likelihood"),
            H("A fixed order contributes once at each queried label"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a finite labelled vertex set and a degree function d. A local order "
                    + "is a bijection from the d(v) positions onto the neighbors of v. The "
                    + "reference run uses a fixed table of valid orders. For the candidate "
                    + "graph, the law is uniform on all tables of valid orders. Each graph "
                    + "therefore has degree d(v) at v.")),
                Paragraph(Text(
                    "Fix one deterministic adaptive protocol that returns the complete "
                    + "ordered list on each query. The probability of the actual reference "
                    + "transcript in the candidate graph is zero when any reported edge is "
                    + "absent. When the candidate contains all reported edges, the probability "
                    + "is the reciprocal of the product of d(v)! over the distinct vertices "
                    + "queried in the reference run. The probability is stated as a finite "
                    + "outer measure.")),
                Paragraph(Text(
                    "The reported edges and degree constrain each queried neighbor set to "
                    + "equal the reference set. Its ordered reply fixes one local permutation. "
                    + "Fixing those permutations replays the same deterministic query branches. "
                    + "The unrestricted coordinates are precisely the unqueried vertices. "
                    + "Repeated queries reuse the order stored at that vertex."))),
            DescribeRole.Theorem))));
}
