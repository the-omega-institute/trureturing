using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class MixedBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/MixedBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual mixed-block graphs and their exhaustive minimal-fort counts.",
        H("Mixed complete and octahedral blocks"),
        Blocks(
            Node("vertices", "The actual labelled vertices", "Vertex", "For arbitrary nonnegative natural x,y,z,r, the base has x disjoint copies of the complete graph on six vertices, twice y disjoint triangles, z disjoint octahedral graphs, and one complete graph on r plus two vertices. The vertex type additionally contains one universal root. Zero multiplicities are permitted. The final complete block is always present.", DescribeRole.Definition),
            Node("graph", "The actual connected graph", "graph", "The graph is the cone over the specified disjoint base. Every root-base edge is present; edges inside each labelled component are exactly those of its complete or octahedral graph; there are no other edges. All graphs are finite, simple, undirected, loopless and unweighted. The natural parameter r is not restricted to the six order residues.", DescribeRole.Definition),
            Node("exact-count", "Exact order and all minimal forts", "mixed_graph_count", "For all nonnegative natural x,y,z,r, the actual graph has order six times the sum x+y+z, plus r plus three, is connected, and its entire minimal-fort count equals (r+2) times 6 to x times 9 to y times 12 to z, plus 15x plus 6y plus 11z plus the binomial coefficient choose(r+2,2). All actual inclusion-minimal nonempty forts are counted. Root-free counts add across components, while root-containing counts multiply. The proof includes arbitrary repeated blocks and zero-copy cases. The exponential root-containing term is used for asymptotic normalization; the root-free term grows at most linearly in the total block multiplicity.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
