using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalTree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique paths reduce the full three-terminal bond law of a finite-edge tree "
            + "to three independent arms, including empty arms and all zero-probability boundaries.",
        H("Three-terminal bond percolation on trees"),
        Blocks(
            Node("path_edge_symmDiff", "The three path edge sets", DescribeRole.Theorem,
                "For every acyclic simple graph G, vertices a,b,c, walks p:a -> b, "
                    + "q:b -> c and r:a -> c that are paths, and undirected edge e, "
                    + "e belongs to r exactly when it belongs to precisely one of p and q. "
                    + "Every path's edges lie in any walk with the same endpoints. "
                    + "Deleting a path edge disconnects its endpoints. No edge can lie "
                    + "in all three terminal paths: the deleted-edge components would then "
                    + "separate all three endpoints across the same cut. These facts give "
                    + "the symmetric difference identity without assuming nonempty arms."),
            Node("bondGraph", "Open subgraph on actual edges", DescribeRole.Definition,
                "For a simple graph G and omega:G.edgeSet -> Bool, bondGraph G omega "
                    + "has exactly those actual edges e of G with omega(e)=true. "
                    + "The definition uses a set of undirected edges and does not add "
                    + "independent random coordinates for nonedges."),
            Node("graphMode", "The five terminal partitions", DescribeRole.Definition,
                "For a graph H and terminals a,b,c, graphMode H a b c reads their "
                    + "path connectivity. It returns all if a reaches b and b reaches c, "
                    + "ab or bc for just that pair, ac for the remaining connected pair, "
                    + "and separate otherwise."),
            Node("bondLaw", "Finite independent source law", DescribeRole.Definition,
                "For a graph G with finite edge type, terminals a,b,c, rates theta:G.edgeSet -> R "
                    + "and mode s, bondLaw G a b c theta s sums the independent Bernoulli "
                    + "product weight over all actual edge configurations omega whose "
                    + "open graph has mode s. With rates in [0,1], this is the actual "
                    + "five-partition probability law."),
            Node("bondLaw_sum", "Normalization of the partition law", DescribeRole.Theorem,
                "For every simple graph with finite edge type, terminals a,b,c and "
                    + "real rates theta, the sum of the five bondLaw masses is one. "
                    + "The five disjoint partition events exhaust all configurations. "
                    + "Rates in [0,1] are additionally needed for nonnegative masses."),
            Node("pathSupport", "Path edges as source indices", DescribeRole.Definition,
                "For every finite-edge graph G and path p, pathSupport p is the finite "
                    + "set of indices e:G.edgeSet whose underlying undirected edge occurs in p."),
            Node("tree_law", "Full law preservation by three arms", DescribeRole.Theorem,
                "For every simple tree G with finite edge type, all vertices a,b,c, "
                    + "and all independent edge rates theta in [0,1], there exist A,B,C "
                    + "in [0,1] such that bondLaw G a b c theta equals the entire star "
                    + "law with rates [A,B,C]. Choose the unique paths p:a -> b and "
                    + "q:b -> c. The rates A,B,C are products of theta over, respectively, "
                    + "P minus Q, P intersect Q, and Q minus P. The third path has edge "
                    + "set P symmetric-difference Q. Independence gives all pair and "
                    + "triple connection probabilities from these products. Normalization "
                    + "then determines all five masses. Empty products equal one, so "
                    + "coincident terminals and terminals at the central branching vertex "
                    + "are included. No probability is divided out."),
            Node("tree_bound", "Uniform constant one for trees", DescribeRole.Theorem,
                "For every simple tree G with finite edge type, all terminals a,b,c, "
                    + "and all rates theta:G.edgeSet -> [0,1], put p=bondLaw G a b c theta "
                    + "and Z=p(ac). Then 0 <= delta(p) <= Z. In particular Z=0 forces "
                    + "delta(p)=0. Full law preservation and the star determinant identity "
                    + "give delta(p)=B(1-AC)Z. The strictly interior star family shows "
                    + "that no smaller uniform constant holds for the class of trees.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-tree-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
