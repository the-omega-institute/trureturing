using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HypercubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Hypercube.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Boolean hypercube of dimension n is regular of degree n and therefore carries "
            + "n times two to the power n minus one edges.",
        H("The Boolean hypercube and its edge count"),
        Blocks(
            Paragraph(Text(
                "Vertices are the Boolean functions on a finite index type and adjacency is "
                    + "Hamming distance one, so the graph is the one-skeleton of the cube. Both "
                    + "facts below follow from that single adjacency condition, the second from "
                    + "the first by the degree-sum identity.")),
            Describe.Lean(
                DescribeId.Create("hypercube-definition"),
                DeclarationHandle.Create(Prefix + "hypercube"),
                H("The hypercube graph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural number n, hypercube n is the simple graph on the Boolean "
                        + "functions from the finite type of size n in which two vertices are "
                        + "adjacent exactly when their Hamming distance equals one. Symmetry comes "
                        + "from symmetry of Hamming distance and irreflexivity from the vanishing "
                        + "of the distance of a vertex to itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hypercube-regularity"),
                DeclarationHandle.Create(Prefix + "hypercube_regular"),
                H("Regularity of degree n"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every vertex of hypercube n has exactly n neighbours. The proof exhibits a "
                        + "bijection from the index type to the neighbour set of a vertex x, "
                        + "sending an index i to the function that agrees with x away from i and "
                        + "negates x at i. That function is adjacent to x because the set of "
                        + "coordinates where the two disagree is the singleton on i. Injectivity "
                        + "follows by evaluating at the index, and surjectivity from the fact that "
                        + "a neighbour disagrees with x on a set of cardinality one, hence on a "
                        + "singleton, and a Boolean value differing from x at that coordinate is "
                        + "its negation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypercube-edge-count"),
                DeclarationHandle.Create(Prefix + "hypercube_edge_count"),
                H("The edge count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The number of edges of hypercube n is n times two to the power n minus one, "
                        + "where the exponent uses truncated subtraction of naturals. Summing the "
                        + "degrees gives twice the edge count; regularity turns the sum into n "
                        + "times the number of vertices, which is n times two to the power n. "
                        + "Dividing by two gives the claim for positive n, and for n equal to zero "
                        + "both sides vanish, so the truncated exponent causes no exception."))),
                DescribeRole.Theorem)),
        []));
}
