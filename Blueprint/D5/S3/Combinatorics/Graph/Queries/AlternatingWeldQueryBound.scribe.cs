using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class AlternatingWeldQueryBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-step probability estimate for an alternating weld.",
        H("A fresh weld edge after complete queries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-weld-completion-neighbor"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_neighbor_mass_le"),
                H("The fresh-neighbor bound for a prescribed subgraph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite vertex set has at least three vertices and is split into "
                        + "two color classes of size n. Let F have at least one undirected "
                        + "alternating full-cycle completion and let f be its number of edges. "
                        + "If f plus two is at most n, there is a uniform law on its alternating "
                        + "completions. Under this law, the outer mass of an edge outside F "
                        + "from x to any vertex of a finite target set S is at most twice "
                        + "the size of S divided by n minus f minus one.")),
                    Paragraph(Text(
                        "Condition on the orientation of the edges of F. The outgoing "
                        + "estimate in each orientation fiber is uniform in the fiber. Reversal "
                        + "then gives the same mass for the incoming event. Every fresh "
                        + "undirected edge belongs to their union."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-weld-query-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound.weld_query_prefix_bound"),
                H("The conditional probability of a fresh weld edge to a target set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a uniform alternating full cycle join two sets of n leaves embedded "
                        + "in a fixed graph. Condition on a positive-mass transcript of q full "
                        + "unordered neighborhood queries. The reference cycle has edges disjoint "
                        + "from the fixed graph. For a leaf x and a finite target set S of leaves, "
                        + "if 2q + 2 is at most n, the conditional mass of a weld edge from x "
                        + "to S absent from the exposed weld is at most 2 times the size of S "
                        + "divided by n minus 2q minus one.")),
                    Paragraph(Text(
                        "The transcript law gives a uniform completion of the exposed weld. "
                        + "Each query contributes at most two weld edges, so the exposed edge "
                        + "count is at most 2q. Orient the completion and condition on the "
                        + "orientation of the exposed edges. In each orientation fiber, a fresh "
                        + "outgoing edge joins the tail of one component to a head in another. "
                        + "Sending each target leaf to its component yields at most as many "
                        + "candidate components as leaves in S. The directed successor bound "
                        + "applies on each fiber. Averaging over the fibers, reversing direction "
                        + "and bounding the mass of the outgoing-or-incoming event gives the "
                        + "undirected estimate."))),
                DescribeRole.Theorem))));
}
