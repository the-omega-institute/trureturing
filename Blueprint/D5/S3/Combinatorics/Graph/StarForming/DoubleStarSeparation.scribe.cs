using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DoubleStarSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DoubleStarSeparation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingcertificates");
    private static DocumentBlock Node(string name, string title, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-vertex double star has dissociation number four, upper two-star-forming "
            + "number four and sub-quorum color maximum five. It disproves the proposed "
            + "coloring comparison on both bipartite and triangle-free graphs.",
        H("A six-vertex separation for the coloring comparison"),
        Blocks(
            Paragraph(Text("The source is the complete public note An elementary global "
                + "certificate bound for 2-star-forming sets, the-omega-institute/"
                + "subquorum-colorings at revision 2e430b6481d4959f05f6d805871117261257e39d, "
                + "docs/STAR_FORMING_CERTIFICATES.md. The graph and all three parameters "
                + "below are exactly those in its double-star example.")),
            Node("doubleStar", "The adjacent centers and four leaves",
                "The vertex type is Fin 6. Centers 0 and 1 are adjacent, leaves 2 and 3 "
                    + "attach to 0, and leaves 4 and 5 attach to 1. There are no other edges. "
                    + "This is the six-vertex double star, distinct from the seven-slot "
                    + "construction that attaches a double star to a base vertex.", DescribeRole.Definition),
            Node("beta_doubleStar", "Dissociation number four",
                "The existing beta doubleStar 2 equals four. The four leaves are an "
                    + "independent set. Every set with at least five vertices contains a "
                    + "selected center with at least two selected neighbours."),
            Node("sf_doubleStar", "Upper two-star-forming number four",
                "The existing SF doubleStar 2 equals four. The four leaves form an "
                    + "inclusion-minimal star-forming set: each outside center sees two "
                    + "leaves, while deleting a leaf leaves that vertex on no path when "
                    + "added back. Every five-set contains a star-forming four-set. If "
                    + "the missing vertex is a center, delete the other center. If the "
                    + "missing vertex is a leaf, delete the opposite center. The full "
                    + "vertex set also contains the four leaves and is not minimal. "
                    + "The finite subset proof uses the existing LocalTwo equivalence."),
            Node("psiSq_doubleStar", "Sub-quorum maximum five",
                "The existing psiSq doubleStar equals five, counting actual represented "
                    + "colors on a partial support. Give both centers one color and give "
                    + "the four leaves four distinct further colors. Six represented "
                    + "colors would force all six vertices to be colored injectively. "
                    + "Then a center has three differently colored neighbors, so its "
                    + "single same-color closed-neighborhood vertex cannot form half "
                    + "of its four colored closed-neighborhood vertices."),
            Node("doubleStar_bipartite", "A proper two-coloring",
                "The double star admits a proper coloring with Fin 2. One side contains "
                    + "0,4,5 and the other contains 1,2,3."),
            Node("doubleStar_triangleFree", "No triangle",
                "The double star is clique-free at three, as follows from its proper "
                    + "two-coloring."),
            Node("exact_parameters", "The complete strict separation",
                "The simultaneous equalities are beta doubleStar 2 equals four, SF "
                    + "doubleStar 2 equals four, and psiSq doubleStar equals five. In "
                    + "particular SF doubleStar 2 is strictly less than psiSq doubleStar."),
            Node("claim", "The two proposed graph-class comparisons",
                "The claim is the disjunction of the universal comparison psiSq G at "
                    + "most SF G 2 on every finite bipartite graph, and the same universal "
                    + "comparison on every finite triangle-free graph. Refuting this "
                    + "disjunction refutes each comparison.", DescribeRole.Definition),
            Node("result", "Both larger graph classes fail the comparison",
                "The six-vertex double star belongs to both classes and has five greater "
                    + "than four, so neither class satisfies the proposed universal "
                    + "inequality. A rectangular-grid comparison still requires a separate "
                    + "proof. No all-grid equality, universal five-sixths theorem, or "
                    + "claim of worldwide novelty or priority follows from this example.")),
        []));
}
