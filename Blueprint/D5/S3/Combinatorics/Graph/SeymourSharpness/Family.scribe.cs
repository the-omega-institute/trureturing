using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SeymourSharpness;

internal sealed class SeymourSharpnessFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SeymourSharpness/Family.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/sadhukhan2026locating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Seymour-distance sharpness for every parameter", H("Exact Seymour-distance sharpness for every parameter"),
        Blocks(
            Paragraph(Text("Theorem 1.2 of the cited paper gives the sharpness construction developed in its Section 3. The stated theorem gives the lower distance bound; its block V_r supplies exact attainment. The result formalizes known mathematics and does not prove the proposed universal upper bound for arbitrary oriented graphs.")),
            Node("family-asymm", "The oriented decreasing-block graph", "family_asymm",
                "There are r+3 blocks arranged in a directed cycle. Their sizes are q, delta, delta-1, through delta-r, and 2delta+1, with delta=3r+2. Block zero is independent; each other block has the short-arc circulant relation. The cross edges are complete from each block to its successor. The resulting relation is asymmetric for every natural q and r. Positivity of q is needed for the finite sharpness theorem, but orientation uses only positivity of the nonzero blocks."),
            Node("family-degrees", "Actual neighborhood counts", "family_degrees",
                "For a vertex in block i, let t_i be zero in block zero and the integer part of (n_i-1)/2 elsewhere. Its first degree is t_i+n_(i+1), and its exact second degree is t_i+n_(i+2), with cyclic indices. These count the graph relation and its literal two-step exact neighborhood."),
            Node("family-sharpness", "Every minimum root has exact distance r", "family_sharpness",
                "Exactly the q vertices of block zero have minimum outdegree delta. For 1<=i<=r, the degree is the integer part of (delta-i)/2 plus delta-i, which exceeds delta. The final two blocks have degrees r+2delta+1 and delta+q. Blocks before r have exact second degree one less than first degree, while block r is Seymour. Each arc stays in its block or advances one block. Projection bounds all walks shorter than r, and successive complete cross edges construct a length-r walk from each minimum root to block r. The dependent finite carrier is nonempty for q positive."),
            Node("exists-sharpness", "The finite-carrier existence theorem", "exists_sharpness",
                "For every positive q and every natural r, there exist n and one asymmetric relation on Fin n whose minimum outdegree is 3r+2, which has exactly q minimum roots, and in which every minimum root has a length-r walk to a Seymour endpoint and every walk to every Seymour endpoint has length at least r. The finite reindexing transports the relation, both neighborhood cardinalities, and directed walks. The selected positive-r statement follows directly. The proof also covers r=0 without an additional hypothesis.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
