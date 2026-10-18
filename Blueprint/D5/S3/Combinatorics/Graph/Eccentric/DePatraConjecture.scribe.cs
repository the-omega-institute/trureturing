using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Eccentric;

internal sealed class DePatraConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Eccentric/DePatraConjecture.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contraction of any bridge whose two deletion components each have at least two "
            + "vertices, followed by addition of one fresh leaf, strictly increases the sum "
            + "of eccentric connected vertex-and-edge subgraph counts.",
        H("De–Patra Conjecture 2.9"),
        Blocks(
            Paragraph(Text("Source: Akash De and Kamal Lochan Patra, On the sum of eccentric "
                + "subgraph numbers of the vertices of a connected graph, arXiv:2610.19694v1, "
                + "Conjecture 2.9, https://arxiv.org/html/2610.19694v1. The mathematical "
                + "argument and its native Lean implementation here are independently written. "
                + "The theorem ranges over every finite simple connected graph and every bridge "
                + "whose two deletion components each have at least two vertices. It imposes "
                + "no tree, girth, cycle, order, or induced-subgraph restriction.")),
            Paragraph(Text("A connected subgraph is an actual SimpleGraph.Subgraph with its "
                + "own vertex set and edge set. Singletons and all permitted non-induced edge "
                + "choices are counted. The pair count f(x,y) counts connected subgraphs "
                + "containing both vertices. Eccentricity is min over every target y, "
                + "including y=x. ES is the sum over all vertices. QualifyingBridge records "
                + "native connectivity, the native bridge predicate, and the two deletion "
                + "reachability-class sizes. contractAddLeaf identifies the endpoints through "
                + "the existing contraction and attaches an Option vertex none only to the "
                + "identified root. bridgeShift is its explicitly proved isomorphic labeling.")),
            Node("old-endpoint", "The original endpoint minima", "bridge_endpoint_minimum",
                "Let A and B be the two deletion components, rooted at u and v. Let a and b "
                + "count their rooted connected subgraphs, and let p and q be their attained "
                + "minimum rooted pair counts to non-root vertices. Singleton exclusion and "
                + "connectivity give 0<p<a, 0<q<b, and a,b at least two. The original endpoint "
                + "eccentricities are min((b+1)p,aq) and min(bp,(a+1)q). Every target in "
                + "either component is bounded below by the relevant expression, including "
                + "the two self targets and the opposite endpoint. The non-root minimizing "
                + "witnesses attain the two displayed candidates."),
            Node("new-root", "The identified-root minimum", "shift_root_endpoint_minimum",
                "The identified root has eccentricity min(2bp,2aq,ab). Targets in A give "
                + "the first candidate, non-root targets in B give the second, and the fresh "
                + "leaf gives ab. The same-side formula includes the self target. Native "
                + "pair-count correspondences prove both the universal lower bound and "
                + "attainment of all three candidates."),
            Node("new-leaf", "The fresh-leaf minimum includes its self target", "shift_leaf_endpoint_minimum",
                "The fresh leaf has eccentricity min(bp,aq). Targets in A give bp and "
                + "non-root targets in B give aq. Its diagonal count is at least the "
                + "pair count ab with the identified root, because forgetting that root "
                + "injects the latter subgraphs into the diagonal subgraphs. Since p<a "
                + "and q<b, that self target cannot decrease the minimum. The singleton "
                + "leaf is included by the underlying native count."),
            Node("joint-endpoints", "The two endpoints improve jointly", "shift_endpoints_strict",
                "Put X=bp and Y=aq. If X<=Y, the old endpoint sum is "
                + "X+min(X+p,Y), while the new sum is X+min(2X,ab). The remaining old "
                + "minimum is less than 2X because b>1 and p>0, and less than ab because "
                + "q<b. If Y<=X, interchange the components to obtain "
                + "Y+min(X,Y+q)<Y+min(2Y,ab). Thus the joint endpoint contribution "
                + "strictly increases, even though the fresh leaf's individual "
                + "contribution can decrease."),
            Node("strict-sum", "The strict total inequality", "dePatra_conjecture_2_9_shift",
                "Every vertex away from both endpoints has strictly increased eccentricity, "
                + "as proved by comparison with every new target, including the fresh leaf. "
                + "Separate the finite sum into the two endpoints and the remaining vertices. "
                + "The remaining sum is nondecreasing and the endpoint pair sum is strictly "
                + "increasing. Therefore ES(G)<ES(bridgeShift(G,u,v))."),
            Node("whole-conjecture", "The entire source conjecture", "dePatra_conjecture_2_9",
                "For every finite simple graph G and every QualifyingBridge G u v, "
                + "eccentricSum(G)<eccentricSum(contractAddLeaf(G,u,v)). The explicit "
                + "bridgeShiftIso and the native isomorphism invariance of the entire "
                + "eccentric sum transport the strict sum theorem to contraction followed "
                + "by a genuinely fresh leaf. No counting identity, source lemma, target "
                + "conclusion, axiom, or unverified graph premise is assumed.")), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
