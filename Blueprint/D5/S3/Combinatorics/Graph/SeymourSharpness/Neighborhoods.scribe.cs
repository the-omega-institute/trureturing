using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SeymourSharpness;

internal sealed class SeymourSharpnessNeighborhoodsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/sadhukhan2026locating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact neighborhoods of dependent compositions", H("Exact neighborhoods of dependent compositions"),
        Blocks(
            Paragraph(Text("A directed composition replaces each base edge by all edges between the corresponding clusters. The clusters may have different carriers and different internal graphs. Exact second neighbors exclude the root and its immediate outneighbors and require a two-edge witness. Walks include length zero.")),
            Node("composition-asymm", "Asymmetry of the composition", "composition_asymm",
                "An asymmetric base and asymmetric internal relations give an asymmetric relation on the dependent sum of the cluster carriers."),
            Node("composition-exact-second", "Exact second-neighbor decomposition", "composition_exact_second",
                "When each cluster is nonempty and the base is asymmetric, exact second neighbors of a vertex consist of its internal exact second neighbors together with all vertices in clusters above exact second neighbors of its base vertex. A path using one internal and one cross edge ends in a first-neighbor cluster and is excluded. A path using two cross edges cannot return to its starting cluster."),
            Node("composition-degrees", "Cardinalities of the disjoint pieces", "composition_degrees",
                "For a finite base and finite nonempty cluster carriers, if the base is asymmetric and its vertex has a unique first-neighbor cluster s and a unique exact second-neighbor cluster t, the global first degree is its internal first degree plus the cardinality of s, and its global exact second degree is its internal exact second degree plus the cardinality of t.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
