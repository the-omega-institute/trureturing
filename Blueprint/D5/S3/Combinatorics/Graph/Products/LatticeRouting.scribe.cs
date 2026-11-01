using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class LatticeRoutingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/LatticeRouting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sparse occupancy checker certifies injectivity and both directions of lattice adjacency.",
        H("Induced lattice routing certificates"), Blocks(
            Paragraph(Text("Points are pairs of integers. Square adjacency means Manhattan distance one. The checker uses complete vertex and oriented-edge lists supplied by the actual graph construction. It neither assumes an embedding nor takes a certificate-correctness record as a hypothesis.")),
            Node("fresh-insert", "Occupancy.insert_spec", "Insertion records a fresh key and preserves old lookups",
                "A successful insertion gives read(next,key)=some(v) and preserves every previous successful lookup. Occupied keys are rejected even when their stored value equals the proposed value. Induction on the key proves this invariant.", DescribeRole.Theorem),
            Node("fill", "Occupancy.fill_spec", "Filling preserves occupancy and stores every listed vertex",
                "Successful fill preserves all old lookups and stores every a in xs at key(a). No injective hash assumption is needed: successful fresh insertion proves the needed uniqueness on the actual occupied vertices.", DescribeRole.Theorem),
            Node("soundness", "routingCheck_sound", "Success proves an induced routing",
                "For arbitrary decidable G and coordinate function c, assume vs contains every vertex and G.Adj(v,w) is equivalent to (v,w) or (w,v) occurring in es. If routingCheck is true, c is injective and, for every v,w, G.Adj(v,w) iff squareAdj(c(v),c(w)). Edge checking proves the forward implication. Four spatial queries per vertex and the fill invariant prove the reverse implication. A retrieved hash-collision value is checked against its actual coordinate.", DescribeRole.Theorem),
            Node("rotation", "rotation_adjacency", "The integral rotation preserves the required adjacency",
                "rotate(x,y)=(x+y+25,x-y+1705). The identity max(abs(a+b),abs(a-b))=abs(a)+abs(b) gives the exact equivalence, including all coordinate signs. The rotation is injective.", DescribeRole.Theorem),
            Node("strong", "strongProduct", "The actual strong product",
                "Adjacency is Mathlib boxProd adjacency or simultaneous adjacency in both factors. Thus one coordinate may stay fixed while the other follows an edge, or both may follow edges. This is the strong product required for king grids.", DescribeRole.Definition),
            Node("finite-paths", "strong_paths_iff", "Finite path factors give king adjacency",
                "For p,q in Fin n times Fin m, the strong product of the pinned Mathlib path graphs is adjacent exactly when the maximum absolute coordinate difference is one.", DescribeRole.Theorem),
            Node("rectangle", "oneBasedRectangleEmbedding", "Convert inclusive bounds into a finite induced embedding",
                "Given coordinate injectivity, exact square adjacency and bounds 1 <= rotate(c(v)).x <= n and 1 <= rotate(c(v)).y <= m for every v, subtract one from both rotated coordinates and obtain a graph embedding into Fin n times Fin m. A graph embedding reflects as well as preserves adjacency. The bounds and local checker remain actual proof obligations in its concrete consumer.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
