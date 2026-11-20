using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Cographs;

internal sealed class CographSeinscheDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Cographs/CographSeinsche.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Cographs/mannamandaltura2026spectralcographs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induced four-vertex paths and the Seinsche cut.",
        H("Induced four-vertex paths and the Seinsche cut"),
        Blocks(
            Entry("IsP4Free", "Induced four-vertex path exclusion",
                "No four distinct vertices induce exactly the three successive edges of a path.", DescribeRole.Definition),
            Entry("IsP4Free.comap", "Pullback",
                "Pulling back the graph along a map preserves induced four-vertex path exclusion."),
            Entry("IsP4Free.induce", "Induced subgraphs",
                "Restricting to a vertex subset preserves induced four-vertex path exclusion."),
            Entry("Iso.isP4Free_iff", "Graph isomorphisms",
                "An isomorphism preserves and reflects the four-vertex path condition."),
            Entry("IsP4Free.compl", "Complementation",
                "The four-vertex path is self-complementary, so its absence is preserved by complementation."),
            Entry("IsP4Free.not_pathGraph_four_isIndContained", "Path exclusion",
                "The four-vertex condition excludes the native induced path graph."),
            Entry("pathGraph_four_isIndContained_of_adj", "Induced path construction",
                "The three successive edges and the required nonedges on four distinct vertices give an induced path embedding."),
            Entry("isP4Free_iff_not_pathGraph_four_isIndContained", "Equivalent path definitions",
                "The explicit four-vertex condition and the native induced-embedding exclusion are equivalent."),
            Entry("Preconnected.exists_neighbor_in_deleted_component", "Neighbors of a deleted vertex",
                "In a preconnected graph each component left after deleting a vertex contains one of its neighbors."),
            Entry("IsP4Free.adj_of_deleted_reachable", "Adjacency inside a deleted component",
                "The induced-path restriction forces the claimed adjacencies along paths in the vertex-deleted graph."),
            Entry("IsP4Free.adj_all_of_not_preconnected_delete", "Completeness to deleted components",
                "When deletion disconnects the graph, the path restriction yields a deleted component entirely adjacent to the deleted vertex."),
            Entry("not_preconnected_compl_of_universal", "Universal vertex in the complement",
                "On a nontrivial carrier the complement of a graph with a universal vertex is disconnected."),
            Entry("compl_induce_eq_induce_compl", "Induction and complementation",
                "Taking the complement commutes with restricting to a vertex subset."),
            Entry("IsP4Free.not_preconnected_or_compl", "Seinsche decomposition",
                "On a finite nontrivial path-free carrier, the graph or its complement fails preconnectedness."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("cographseinsche-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
