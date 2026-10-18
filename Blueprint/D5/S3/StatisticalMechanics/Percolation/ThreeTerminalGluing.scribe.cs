using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalGluing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A network attached through one gate changes the entire terminal partition "
            + "by one deterministic operation, simultaneously preserving its three connection relations.",
        H("Three-terminal partitions across one gate"),
        Blocks(
            Node("OneVertexUnion", "One shared gate", DescribeRole.Definition,
                "For arbitrary vertex type V, simple graphs H,K on V, subsets A,B of V "
                    + "and gate g in V, OneVertexUnion H K A B g asserts that every H edge "
                    + "has both endpoints in A, every K edge has both endpoints in B, "
                    + "and every vertex in both A and B equals g. The sides need not "
                    + "cover isolated vertices, and no finiteness or terminal distinctness is assumed."),
            Node("simultaneous_reachability", "All three connection identities", DescribeRole.Theorem,
                "For every OneVertexUnion H K A B g and terminals a,b in A and c in B, "
                    + "a reaches b in H union K exactly when it does in H; a reaches c "
                    + "in H union K exactly when a reaches g in H and g reaches c in K; "
                    + "and b reaches c in H union K exactly when b reaches g in H and "
                    + "g reaches c in K. These three equivalences hold together for "
                    + "the same realized graphs. Collapse the vertices outside A to g. "
                    + "An H edge remains an H connection, and a K edge collapses to "
                    + "the reflexive connection at g because its endpoints in A must equal g. "
                    + "Induction on a union-graph walk produces the H-side connection. "
                    + "The exchanged collapse produces the K-side connection. Conversely, "
                    + "concatenating the two gate connections gives the union connection. "
                    + "Reflexive reachability includes terminals that coincide with the gate."),
            Node("graphMode_pendant", "Exact five-partition replacement", DescribeRole.Theorem,
                "Under the same hypotheses, graphMode of (a,b,c) in H union K equals "
                    + "graphMode of (a,b,g) in H if g reaches c in K. Otherwise the old "
                    + "all or ab mode becomes ab, and the old ac, bc or separate mode "
                    + "becomes separate. The conclusion is pointwise in the realized "
                    + "graphs and preserves the whole five-mode law after any common "
                    + "probabilistic pushforward. The proof consumes the simultaneous "
                    + "connection identities; agreement of separate marginal probabilities "
                    + "is not its premise. This is the deterministic bridge for replacing "
                    + "an independently attached network by its actual gate-to-terminal "
                    + "connection bit. Independence and its Bernoulli rate require a "
                    + "separate product-measure argument."),
            Node("actualEdgeEnds", "Orienting the actual edge coordinates", DescribeRole.Definition,
                "For every simple graph G on V and actual edge e:G.edgeSet, "
                    + "actualEdgeEnds G e chooses a representative ordered pair of "
                    + "the undirected edge e. Its symmetric pair is exactly e. The "
                    + "coordinate type remains G.edgeSet, so nonedges receive no "
                    + "random bit and distinct edge indices remain distinct."),
            Node("actual_edge_graph", "The same actual open graph", DescribeRole.Theorem,
                "For every simple graph G on an arbitrary vertex type and every Boolean "
                    + "configuration on its actual edges, openGraph(actualEdgeEnds G) "
                    + "equals bondGraph G on the same configuration. Each chosen ordered "
                    + "representative restores exactly the original unordered edge, and "
                    + "open-state coordinates are neither added nor removed."),
            Node("actual_edge_law", "The two graph-source interfaces agree", DescribeRole.Theorem,
                "For every finite vertex type V with decidable equality, simple "
                    + "graph G with a finite decidable actual edge type, terminals a,b,c "
                    + "and arbitrary real edge rates theta, the complete law of the "
                    + "endpoint network actualEdgeEnds G equals bondLaw G a b c theta. "
                    + "For each configuration the open endpoint graph equals bondGraph "
                    + "G on that same configuration: restoring each chosen representative "
                    + "as an unordered pair recovers exactly its original actual edge. "
                    + "Both interfaces then read the same three path connections and "
                    + "sum the same weights over the same configuration cube. No "
                    + "independence or law is manufactured by this interface conversion.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-gluing-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
