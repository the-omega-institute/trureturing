using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphSuspensionMovesModelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite local subgraphs and maximal independent sets", H("Finite local subgraphs and maximal independent sets"), Blocks(
            Node("n0", "embeddedIso", "An embedded edge subgraph",
                "An injective map of a finite model graph into a finite graph defines the subgraph containing exactly the model edges. The model is isomorphic to that local subgraph. Extra ambient edges between its vertices are retained outside the subgraph."),
            Node("n1", "embedded_complement", "Apex complement membership",
                "For each maximal independent set of the model, membership outside its transported apex set is exactly membership in the image of the model complement."),
            Node("n2", "edgeMaxEquiv", "One edge",
                "The single edge has exactly two maximal independent sets, the singleton endpoints."),
            Node("n3", "quadrantMaxEquiv", "Two disjoint edges",
                "The two-edge matching has exactly four maximal independent sets, choosing one endpoint on each edge. Ambient cross edges do not enter this model."),
            Node("n4", "starMaxEquiv", "A nonempty star",
                "A star with a finite nonempty leaf set has exactly two maximal independent sets: its center and its entire leaf set."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
