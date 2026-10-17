using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Eccentric;

internal sealed class DePatraBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Eccentric/DePatraBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected vertex-and-edge subgraphs admit an exact decomposition at a single shared root. "
            + "Their eccentric counts are invariant under graph isomorphism, and the two endpoint "
            + "minimum expressions in the bridge transformation satisfy a strict joint inequality.",
        H("Connected Subgraph Counts at a Bridge"),
        Blocks(
            Paragraph(Text("The source question is Conjecture 2.9 of Akash De and Kamal Lochan Patra, "
                + "On the sum of eccentric subgraph numbers of the vertices of a connected graph, "
                + "arXiv:2610.19694v1, https://arxiv.org/html/2610.19694v1. The mathematical "
                + "definitions and proofs here are independently written. The source problem "
                + "ranges over finite simple connected graphs and a bridge whose two deletion "
                + "components each contain at least two vertices. Identifying the endpoints and "
                + "adding one new pendant vertex is asserted to increase the eccentric sum strictly.")),
            Node("actual-counts", "Actual connected subgraphs", "countContaining",
                "For a graph G and a set s of specified vertices, countContaining(G,s) is Nat.card "
                + "of the subtype of G.Subgraph consisting of connected subgraphs K with s contained "
                + "in K.verts. A subgraph records its own vertices and edges. All permitted edge "
                + "subsets are counted separately, and no inducedness condition is imposed. "
                + "Singleton subgraphs are included by the native connectivity predicate.", DescribeRole.Definition),
            Node("eccentric-counts", "Every target, including the diagonal", "eccentricity",
                "The pair count is countContaining(G,{x,y}). The eccentricity of x is the infimum "
                + "of these natural numbers over every y in the entire vertex type. The self target "
                + "y=x is included. The range is nonempty because x itself is a target, and its "
                + "minimum is attained. eccentricSum is the finite sum of these eccentricities.", DescribeRole.Definition),
            Node("root-bounds", "The singleton gives strict root bounds", "rootMinimum_bounds",
                "For any finite connected graph G, a root r, and an existing vertex distinct "
                + "from r, let p be the minimum pair count from r to the non-root vertices and "
                + "a the pair count from r to itself. Then 0<p<a and 2<=a. The full connected "
                + "graph witnesses positivity. Forgetting a distinct target injects its subgraphs "
                + "into the rooted subgraphs, and the singleton root lies outside that injection.", DescribeRole.Theorem),
            Node("source-components", "The exact deletion components", "qualifying_components",
                "QualifyingBridge uses native connectivity, the native IsBridge predicate, and "
                + "the cardinalities of the two endpoint reachability classes after deleting "
                + "the bridge. For every qualifying graph these classes cover all vertices, "
                + "are disjoint, and their induced deletion graphs are connected. Each has "
                + "a non-root vertex because its cardinality is at least two. Thus the "
                + "hypotheses describe precisely the two deletion components in the source.", DescribeRole.Theorem),
            Node("source-operation", "Contraction followed by a fresh leaf", "bridgeShiftIso",
                "For every simple graph G and distinct vertices u,v, bridgeShift(G,u,v) is "
                + "isomorphic to contractAddLeaf(G,u,v). The latter first uses the existing "
                + "endpoint contraction on the vertices different from v and then adds an Option "
                + "vertex none adjacent only to the image of u. The explicit isomorphism sends "
                + "v to none and every other x to some(x). Thus v in bridgeShift names a fresh "
                + "pendant vertex, and its former incident edges are redirected to u.", DescribeRole.Theorem),
            Node("isomorphism", "Counts and their sum respect isomorphism", "eccentricSum_iso",
                "For arbitrary finite vertex types and a graph isomorphism e:G->H, "
                + "eccentricSum(G)=eccentricSum(H). Mapping both vertices and edges defines "
                + "inverse bijections between actual subgraphs. Connectivity and specified-vertex "
                + "containment are preserved. Pair counts agree under e, minima agree because "
                + "every target has an inverse image, and the vertex sum agrees by reindexing.", DescribeRole.Theorem),
            Node("rooted-gluing", "Independent edge choices on the two sides", "rootedGluing_count",
                "Let S,T cover the vertex type, both contain r, and have intersection exactly "
                + "{r}. Suppose every graph edge has both endpoints in S or both in T. For every "
                + "target set s, connected subgraphs containing r and s correspond bijectively "
                + "to pairs of connected subgraphs supported on S and T containing r and "
                + "respectively s intersect S and s intersect T. Their cardinality is the "
                + "product of the two cardinalities. Restriction intersects the vertex set "
                + "and retains exactly the chosen internal edges. A walk on either side is "
                + "obtained by collapsing the other side to r, omitting repeated vertices. "
                + "Union reconstructs both vertex and edge sets. Cycles and omitted edges "
                + "inside either side are allowed.", DescribeRole.Theorem),
            Node("bridge-count", "Native bridge counting decomposition", "bridge_rooted_count",
                "For every QualifyingBridge G u v and every target set s, the rooted count "
                + "at u in the entire graph is the product of the two local rooted counts. "
                + "The first side is the deletion component containing u; the second is the "
                + "deletion component containing v together with u and the bridge. Their "
                + "intersection is exactly u. Deletion reachability proves the required "
                + "partition of every edge, so this is a specialization to the actual source "
                + "bridge rather than an assumed product formula.", DescribeRole.Theorem),
            Node("unrooted-gluing", "Targets on one side", "within_gluing_count",
                "Under the same separation assumptions, let the nonempty target set s lie "
                + "in S. The total number of connected subgraphs containing s is the number "
                + "of rootless such subgraphs supported in S, plus the product of the rooted "
                + "counts on S and T. A connected subgraph containing a vertex of S and "
                + "omitting r cannot leave S. Partitioning by membership of r and using the "
                + "rooted bijection proves the identity without assuming a counting formula.", DescribeRole.Theorem),
            Node("endpoint-comparison", "Compare both endpoints jointly", "endpoint_minima_strict",
                "For natural numbers a,b,p,q with a,b at least 2, 0<p<a, and 0<q<b, "
                + "min((b+1)p,aq)+min(bp,(a+1)q) is strictly smaller than "
                + "min(2bp,2aq,ab)+min(bp,aq). Splitting into bp<=aq and aq<=bp gives "
                + "a common summand. In the first case the remaining old minimum is less "
                + "than both 2bp and ab; in the second it is less than both 2aq and ab. "
                + "This compares the endpoint pair as a whole and permits the fresh leaf's "
                + "individual contribution to decrease.", DescribeRole.Theorem),
            Paragraph(Text("These foundational counting and arithmetic results are consumed "
                + "by DePatraCounting and DePatraConjecture. The latter proves the entire "
                + "source conjecture for every qualifying bridge, including the comparison "
                + "against every target and transport to contraction followed by a fresh leaf. "
                + "No source lemma or counting identity is assumed."))), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
