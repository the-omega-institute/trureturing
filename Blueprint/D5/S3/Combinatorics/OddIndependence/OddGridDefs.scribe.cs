using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.OddIndependence;

internal sealed class OddGridDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OddIndependence/OddGridDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependencegrids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square grid and a vanishing density correction express the full-cross question of Caro, Petrusevski, Skrekovski and Tuza.",
        H("Dense independent sets and four-neighbour crosses"),
        Blocks(
            Node("odd-grid-graph", "The square grid", "grid",
                "For a natural number n, the graph is the Cartesian product of two paths on n vertices. Its vertices are pairs (a,b) with coordinates from zero through n-1. Two vertices are adjacent when one coordinate is equal and the other differs by one. Boundary vertices can have fewer than four neighbours.", DescribeRole.Definition),
            Node("odd-grid-claim", "The vanishing density correction", "claim",
                "There exists a real sequence epsilon indexed by the natural numbers and tending to zero such that, for every n at least one and every independent vertex set S of the n by n square grid, cardinality at least (3/8 + epsilon(n))n squared implies that some vertex has at least four neighbours and every one of its neighbours belongs to S. Since square-grid vertices have at most four neighbours, the conclusion is a full four-neighbour cross, including the requirement that its centre is an interior vertex.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
