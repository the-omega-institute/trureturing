using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeletionResilientCliques;

internal sealed class CriticalVertexCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound on the vertex-cover number has a small supporting subgraph.",
        H("Small witnesses for vertex-cover number"),
        Blocks(
            Describe.Lean(DescribeId.Create("small-cover-witness"),
                DeclarationHandle.Create(Prefix + "exists_small_cover_witness"),
                H("Small witnesses for vertex-cover number"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Hamming/erdosgallai1961vertexcovers")),
                Blocks(Paragraph(Text("For a finite graph G and a positive integer r at most its vertex-cover number, there is a subgraph with vertex-cover number exactly r and at most 2r nonisolated vertices. Choose an edge-minimal subgraph whose cover number is at least r. Deleting one edge drops the number below r, and restoring one endpoint to a cover shows that the original number is r. For the support bound, the edge-critical condition yields Hall's inequalities between the vertices of a minimum cover and the remaining support vertices. The resulting injection bounds the support by twice the cover size."))), DescribeRole.Theorem)),
        []));
}
