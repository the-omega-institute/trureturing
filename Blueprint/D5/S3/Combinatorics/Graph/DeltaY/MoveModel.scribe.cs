using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeltaY;

internal sealed class MoveModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeltaY/MoveModel.";
    private static readonly LibraryNoteRef Zhou =
        LibraryNoteRef.Create("D5/L/Rewriting/zhou2026deltay");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle-star moves on finite simple graphs and their representation by finite active labels.",
        H("Triangle-star graph moves"),
        Blocks(
            Node("delta-y-forward", "Triangle to star", "ForwardSpec", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Zhou),
                "An equivalence from Option of the starting vertex type to the target vertex type identifies the survivors and the fresh center. The three old triangle edges are deleted. The center is joined to precisely the three triangle vertices."),
            Node("delta-y-reverse", "Star to triangle", "ReverseSpec", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Zhou),
                "An equivalence from Option of the surviving vertex type to the starting vertex type identifies the removed center. Its entire neighborhood is the designated triple. Survivor adjacency in the target is the union of old adjacency and all three pairs of the triple."),
            Node("delta-y-strong", "Ordinary and strong moves", "GraphMove", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Zhou),
                "Every forward move is allowed in both relations. A strong reverse move requires the three neighbors to form an independent set before the move."),
            Node("delta-y-transport", "Invariance under relabeling", "transport", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Zhou),
                "Isomorphisms of the initial and final graphs transport a move and preserve its strength. Every finite graph also has a representation by finite active natural labels and unordered edges."),
            Node("delta-y-reverse-degree", "Degree of a reverse center", "source_reverse_degree_three",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Zhou),
                "The Option equivalence lists every vertex of the starting graph. The center consequently has precisely the three distinct neighbors in the reverse site."),
            Node("delta-y-edge-count", "Edge count along strong histories", "source_strong_edge_count",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Zhou),
                "A forward move exchanges three triangle edges for three spokes. A strong reverse move exchanges three spokes for three fresh edges. Hence every finite strong history preserves the number of edges.")),
        []));

    private static DocumentBlock Node(string id, string title, string name, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(prose))), role);
}
