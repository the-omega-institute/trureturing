using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Eccentric;

internal sealed class SubgraphCoreBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/pandeypatra2021subgraphcore");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire maximizing set of actual connected-subgraph counts lies in one block.",
        H("The Subgraph Core and Native Blocks"),
        Blocks(
            Paragraph(Text("Dinesh Pandey and Kamal Lochan Patra, Some new central parts of connected graphs, "
                + "arXiv:2110.00738v1, https://arxiv.org/pdf/2110.00738v1, page 9, state: "
                + "Conjecture 3.25. The subgraph core of a graph G is contained in a block of G. "
                + "Definition 3.23 on that page counts connected subgraphs containing a vertex. "
                + "Page 1 specifies finite simple connected undirected graphs, defines a cut vertex "
                + "by disconnection after deletion, and defines a block as a maximal subgraph with no cut vertex.")),
            Node("number", "Actual vertex and edge choices", "subgraphNumber",
                "For every finite simple graph G and vertex v, subgraphNumber(G,v) is the cardinality "
                + "of the actual connected subgraphs containing v. It uses countContaining(G,{v}) "
                + "from DePatraBridge. Each subgraph has its own vertex set and edge set. Distinct "
                + "edge choices are distinct objects, inducedness is not required, and singleton "
                + "subgraphs are included.", DescribeRole.Definition),
            Node("core", "The entire maximizing set", "subgraphCore",
                "A vertex v belongs to subgraphCore(G) precisely when subgraphNumber(G,w) is at "
                + "most subgraphNumber(G,v) for every vertex w of G.", DescribeRole.Definition),
            Node("block", "Maximal connected subgraphs without a cut vertex", "NativeBlock",
                "NoCut(H) means that H is connected and deleting any one vertex leaves no pair "
                + "of mutually unreachable remaining vertices. Deletion restricts both the actual "
                + "vertex set and the actual edges. NativeBlock(H) means maximality for NoCut "
                + "under subgraph inclusion, including both vertices and edges. Empty deletion "
                + "has no disconnected pair. Thus a one-vertex graph has its singleton block, "
                + "and a bridge edge is admitted as a block. No order cutoff is imposed.", DescribeRole.Definition),
            Node("result", "One block contains all maximizers", "result",
                "For every finite vertex type V and every connected simple graph G on V, "
                + "there exists a native block B of G with subgraphCore(G) contained in B.verts. "
                + "The block is shared by the entire maximizing set.", DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pandey-patra-2021-subgraph-core"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The counting argument extends a connected subgraph H containing x and "
                + "omitting r along a path from r to x, stopping at its first encounter with H. "
                + "Let L be the path before that encounter and K the union of the path with H. "
                + "Then K contains r and x, L contains r and omits x, and deleting L's vertices "
                + "from K recovers H, including its edge choices. This injects the x-only "
                + "subgraphs into pairs consisting of an r-and-x subgraph and an r-only subgraph. "
                + "Writing d for the former count and a for all r-containing subgraphs gives "
                + "the bound c <= d(a-d) for the x-only count c.")),
            Paragraph(Text("At a one-vertex separation with root r, write a and b for the local "
                + "root counts on the two sides, and d and e for the local joint counts at "
                + "r,x and r,y. Exact gluing gives f(r)=ab, f(x)=c+db and f(y)=h+ea. "
                + "The path-extension bound gives c <= d(a-d) and h <= e(b-e). The root "
                + "singletons give d<a and e<b. If both f(x) and f(y) were at least f(r), "
                + "these inequalities would force b<=d<a<=e<b, a contradiction. Hence "
                + "maximizers different from r cannot lie in different components after deleting r.")),
            Paragraph(Text("For a maximizing set with at least two vertices, take the union of "
                + "all simple paths between maximizing vertices. Every vertex on such a path, "
                + "after deleting a vertex z, can still reach one endpoint different from z "
                + "along that path. All maximizing vertices different from z are mutually "
                + "reachable after deleting z by the separation argument, and their connecting "
                + "simple paths belong to the same union. The induced graph on this union "
                + "therefore has no cut vertex. A singleton maximizing set starts with its "
                + "singleton subgraph. Finiteness extends either subgraph to a maximal one."))), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? openProblemResolutionClaim = null) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            declaration == "result" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: openProblemResolutionClaim);
}
