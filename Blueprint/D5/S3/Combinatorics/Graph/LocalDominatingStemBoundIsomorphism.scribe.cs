using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundIsomorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundIsomorphism.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a stem with a unique leaf, the original graph is exactly its one-copy hub graph up to vertex labels.",
        H("The one-copy hub isomorphism"),
        Blocks(
            Node("restored-labels", "Restoring the original vertex labels", "oneCopyMap",
                "For every finite vertex type V, simple graph G, and v,w∈V, the map "
                    + "from (Fin(1)×remaining(G,v))⊕Fin(2) to V sends (i,x) to x, "
                    + "the right vertex 0 to v, and the right vertex 1 to w.",
                DescribeRole.Definition),
            Node("one-copy-isomorphism", "The one-copy graph isomorphism", "oneCopyIso",
                "For every finite V, graph G, and v,w∈V, suppose leafNeighbors(G,v)={w}. "
                    + "Write H for G induced on remaining(G,v), and U for the residual "
                    + "neighbors of v. Restoring the vertex labels gives an isomorphism "
                    + "from replicated(H,U,1) to G. Residual vertices cannot equal v or w; "
                    + "the unique leaf w has no neighbor other than v. All other adjacencies "
                    + "are exactly the original adjacencies retained in H or incident to v.",
                DescribeRole.Definition),
            Node("one-copy-average", "Preservation of the global average", "one_copy_avd",
                "For every finite V, graph G, and v,w∈V with leafNeighbors(G,v)={w}, "
                    + "avd(replicated(residualGraph(G,v),residualNeighbors(G,v),1))=avd(G). "
                    + "A graph isomorphism bijects dominating sets and preserves their cardinalities.",
                DescribeRole.Theorem),
            Node("global-extremality", "Global equality from the replicated graph", "global_equality_from_replication",
                "For every finite V, graph G, and v∈V, suppose leafCount(G,v)=1, "
                    + "partialDomSets(G,v)=residualDomSets(G,v), and the mean size of the "
                    + "residual dominating sets equals 2|remaining(G,v)|/3. Then avd(G)=2|V|/3. "
                    + "The one-copy average has equal counting bases and both residual means "
                    + "equal 2h/3. Its exact formula reduces to 2(h+2)/3, where h is the "
                    + "residual order; the graph isomorphism transfers this equality to G.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
