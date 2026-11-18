using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class EndpointSplitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Incidence/EndpointSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint partitions split a simple graph into tagged blocks.",
        H("Splitting a root graph at its endpoint partitions"),
        Blocks(
            Describe.Lean(DescribeId.Create("endpoint-split-partition"), DeclarationHandle.Create(Owner + "EndpointPartition"),
                H("A setoid at each endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each vertex take a setoid on the edges incident to it. Its quotient has one element per nonempty class. A tagged block is a vertex together with one of its quotient classes. The split graph joins the two tagged classes of each edge. Projecting a split edge to the two tags recovers the original edge, so simple roots give a bijection of edge sets."))),
                DescribeRole.Definition),
            Node("endpoint-split-members-nonempty", "members_nonempty", "Blocks are inhabited",
                "Each block has at least one member, by quotient surjectivity."),
            Node("endpoint-split-pair-membership", "mem_splitPair_iff", "Membership in a split edge",
                "A tagged block belongs to the split pair of a root edge exactly when the edge is incident at its tag and its incident label has that quotient class."),
            Node("endpoint-split-edge-count", "card_edgeSet", "The split preserves edge count",
                "The split graph and the root have the same edge cardinality."),
            Node("endpoint-split-forward-connectivity", "splitGraph_connected_of_steps", "Lifting connectivity to the split",
                "A connected graph on the root edges gives a connected split graph if every adjacent pair of labels has a common split block. Use the adjacency step through that block and both ends of a split edge."),
            Node("endpoint-split-reverse-connectivity", "connected_of_splitGraph_connected", "Projecting connectivity from the split",
                "A connected split graph gives a connected graph on root edges if every block has connected member labels there. Follow a split walk and transfer each step across the label it shares."),
            Node("endpoint-split-incidence-count", "card_total_members", "Each root edge contributes two labels",
                "Over a finite root, the sum of the block member cardinalities is twice the edge count, by the equivalence with marked endpoint incidences."))));

    private static DocumentBlock Node(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
