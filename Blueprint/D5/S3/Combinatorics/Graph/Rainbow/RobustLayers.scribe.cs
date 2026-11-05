using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Rainbow;

internal sealed class RobustLayersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Rainbow/RobustLayers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exterior robust expansion gives an early layer covering every incoming star, while each vertex outside the initial star has a strictly earlier robust rank.",
        H("Early Robust Layers with the Original Vertex Count"),
        Blocks(
            Paragraph(Text("Let G be a directed relation on a finite vertex type V, and put n equal to the cardinality of V. For a finite vertex set T, predecessors(G,T,w) consists of the vertices x in T with an edge x to w. The robust neighbourhood at threshold t consists of all w having at least tn such predecessors. Its normalization is always n. Exterior expansion with parameters nu and tau means that every T of size between tau n and (1-tau)n has at least nu n robust neighbours outside T. Define L(0) as the outgoing neighbours of a fixed root u, and L(i+1) as L(i) union its robust neighbourhood at threshold nu.")),
            Describe.Lean(DescribeId.Create("graph-parameter-bounds"),
                DeclarationHandle.Create(Prefix + "graph_parameter_bounds"),
                H("The Integer Boundary of Exterior Expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose nu and tau are positive, nu+tau is at most alpha, G has no loops, exterior expansion holds, and the outgoing degree of one vertex u is at least alpha n. Then nu is less than one half and alpha n is strictly greater than 2 nu n minus one. Looplessness gives alpha n plus one at most n. If the expansion interval contains an integer, take a set of size floor((1-tau)n) and compare its exterior robust neighbourhood with its complement. This gives nu n less than tau n plus one. If that integer is below tau n, use floor(n/2) to obtain tau n greater than (n-1)/2 instead. Thus the strict inequalities also hold when no integer lies in the expansion interval."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("earlier-rank"),
                DeclarationHandle.Create(Prefix + "earlier_rank"),
                H("An Actual Layer Entry Gives an Earlier Rank"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite directed relation, real threshold nu, vertices u and x, and natural index i, if x belongs to L(i) but not to L(0), there is a natural j strictly below i such that x belongs to the robust neighbourhood of L(j) at threshold nu. Induct on the actual union recurrence. Membership inherited from the preceding layer uses the induction hypothesis; new membership uses the preceding index itself. No expansion or positivity assumption is needed for this entry statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("early-covering-layer"),
                DeclarationHandle.Create(Prefix + "early_covering_layer"),
                H("Stop Early Enough to Reserve One Terminal Edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose nu is positive and less than one half, nu+tau is at most alpha, alpha n is strictly greater than 2 nu n minus one, nu n exceeds four, exterior expansion holds, and every outgoing and incoming degree is at least alpha n. For every root u there is a natural m with m+2 at most floor(1/nu), with L(m) of size at least (1-alpha+nu/2)n, and with every vertex in the robust neighbourhood of L(m) at threshold nu/2. Before this size threshold each layer lies in the expansion interval, and its union recurrence adds at least nu n exterior vertices. Iterating to floor(1/nu)-2 contradicts failure of the threshold. Finally the minimum incoming degree loses at most n minus the layer size outside that layer. These bounds reserve an edge after the subsequent rank construction."))), DescribeRole.Theorem))));
}
