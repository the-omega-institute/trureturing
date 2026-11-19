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
                        "Embed two color classes of n leaves in a fixed finite graph. Fix a "
                        + "deterministic adaptive protocol that receives complete unordered "
                        + "neighborhoods. A reference alternating full cycle has embedded edges "
                        + "disjoint from the fixed graph. Running the protocol on their union "
                        + "gives a transcript T of q queries. The exposed weld consists of edges "
                        + "reported in T outside the fixed graph, pulled back to the leaves.")),
                    Paragraph(Text(
                        "Sample a uniform alternating full cycle and condition on its union "
                        + "with the fixed graph producing T under the same protocol. If this "
                        + "event has positive mass and 2q plus two is at most n, a given leaf x "
                        + "and finite target set S of leaves satisfy the following bound. The "
                        + "conditional mass of a weld edge from x to S outside the exposed weld "
                        + "is at most twice the size of S divided by n minus 2q minus one.")),
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
