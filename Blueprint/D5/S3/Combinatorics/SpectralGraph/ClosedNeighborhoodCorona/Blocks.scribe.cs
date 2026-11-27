using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona;

internal sealed class CoronaBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks.";
    private static readonly LibraryNoteRef SonarSrivastava =
        LibraryNoteRef.Create("D5/L/AdjacencyProduct/sonarsrivastava2024closedneighbourhoodcorona");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjacency blocks and vertex degrees of the closed-neighborhood corona.",
        H("Closed-neighborhood corona blocks"),
        Blocks(
            Theorem("corona-adjacency-blocks", "adjMatrix_corona", "Adjacency blocks",
                "The base block is the base adjacency matrix. The cross block repeats each column "
                + "of the base adjacency plus the identity for all vertices in the indexed copy. "
                + "The opposite cross block is its transpose. The copy block is the Kronecker "
                + "product of the base identity and the attached adjacency matrix. Sonar and "
                + "Srivastava display the identity in §3.1 with the copy coordinates ordered "
                + "as (attached vertex, base vertex). Swapping those coordinates for rows and "
                + "columns gives the arrangement here. Lean proves the identity directly over "
                + "a semiring from the corona adjacency relation.",
                AssessedProvenance.FromLiterature(SonarSrivastava)),
            Theorem("corona-base-degree", "degree_corona_inl", "Degree of a base vertex",
                "A base vertex of degree d keeps its original neighbors and is adjacent to every "
                + "vertex in each of d + 1 copies. If the attached graph has m vertices, its degree "
                + "in the corona is d + (d + 1)m."),
            Theorem("corona-copy-degree", "degree_corona_inr", "Degree of a copy vertex",
                "A vertex of internal degree e in a copy at a base vertex of degree d meets "
                + "the d + 1 base vertices in that closed neighborhood. Its degree is d + 1 + e."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
