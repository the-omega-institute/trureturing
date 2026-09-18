using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class LoopyGeneralizedDegreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two eight-vertex trees, each carrying a single loop, have one common ordinary Loopy "
            + "polynomial and two different generalized degree polynomials.",
        H("Ordinary Loopy equality leaves the generalized degree polynomial free"),
        Blocks(
            Paragraph(Text(
                "The generalized degree polynomial of Crew records, for every subset S of the "
                    + "vertex set, the size of S, the number of edges with both endpoints in S, "
                    + "and the number of edges with exactly one endpoint in S. A loop lies inside "
                    + "S exactly when its vertex does, and never crosses. Two graphs carry the same "
                    + "generalized degree polynomial exactly when these exponent triples agree with "
                    + "multiplicity, so the multiset of triples is a faithful record of it.")),
            Paragraph(Text(
                "The two graphs below are trees on the vertices 0 through 7 with one loop each. "
                    + "Both have degree multiset 1, 1, 1, 1, 2, 2, 3, 5. Running the "
                    + "deletion-contraction recursion of the ordinary Loopy polynomial to its "
                    + "128 leaves gives one and the same polynomial of 25 monomials. The exponent "
                    + "triples separate them: among the subsets of size two that span two inside "
                    + "edges and two crossing edges there is exactly one for the first graph and "
                    + "exactly two for the second.")),
            Def("inside", "Edges inside a subset", "inside",
                "inside E ell S counts the edge occurrences with both endpoints in S and adds the "
                    + "accumulated loops carried by the members of S."),
            Def("crossing", "Edges leaving a subset", "crossing",
                "crossing E S counts the edge occurrences with exactly one endpoint in S. A loop "
                    + "never contributes."),
            Def("gd-triples", "The exponent triples of the generalized degree polynomial", "gdTriples",
                "gdTriples maps every subset of the vertex set to the triple of its size, its "
                    + "inside count and its crossing count, retaining multiplicity."),
            Def("vertices", "The common vertex set", "V",
                "V is the eight vertices 0 through 7."),
            Def("first-graph", "The first graph", "EG",
                "EG is a tree on V with one loop at vertex 1; the loop is stored as the pending "
                    + "edge occurrence from 1 to 1, and the remaining seven occurrences are "
                    + "0-1, 0-5, 1-2, 1-4, 2-3, 5-6 and 5-7."),
            Def("second-graph", "The second graph", "EH",
                "EH is a tree on V with one loop at vertex 4; the remaining seven occurrences are "
                    + "0-1, 0-4, 0-7, 1-2, 2-3, 4-5 and 4-6."),
            Def("claim", "The determination claim", "claim",
                "claim asserts that for independent vertex sets, edge lists and loop accumulators, "
                    + "two valid encodings with equal ordinary Loopy polynomials have equal "
                    + "exponent-triple multisets. There is no looplessness, connectedness, "
                    + "simplicity or equal-order premise."),
            Describe.Lean(
                DescribeId.Create("loopy-generalized-degree-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The determination claim is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both encodings retain every endpoint and store no loops away from the vertex "
                        + "set. The deletion-contraction recursion, run to its leaves on each graph, "
                        + "yields the same polynomial, so the hypothesis of the claim is met. The "
                        + "exponent-triple multisets differ, which contradicts its conclusion. "
                        + "Eight vertices is the smallest order at which this happens among trees "
                        + "carrying a single loop: at orders three through seven every pair with a "
                        + "common ordinary Loopy polynomial also has a common exponent-triple "
                        + "multiset."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Def(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("loopy-generalized-degree-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
