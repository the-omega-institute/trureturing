using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.OddIndependence;

internal sealed class OddGridPaddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OddIndependence/OddGridPadding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependencegrids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation by two places a finite square-grid set in a zero-padded array and preserves full four-neighbour crosses.",
        H("From padded coordinates to square-grid neighbourhoods"),
        Blocks(
            Node("odd-grid-padded", "The translated occupancy array", "padded",
                "For a finite vertex set S in the n by n square grid, padded(S,x,y) is true precisely when (x,y) is the translate (a+2,b+2) of some vertex (a,b) in S. It is false elsewhere. Thus rows and columns with coordinates zero or one are unoccupied, as are all positions with either coordinate at least n+2.", DescribeRole.Definition),
            Node("odd-grid-cross-of-padded", "A padded cross has an interior centre", "cross_of_padded",
                "For any finite grid vertex set S and natural coordinates x,y, suppose the four padded positions (x,y+1), (x+1,y), (x+1,y+2), and (x+2,y+1) are occupied. There exists a vertex of the original grid with at least four neighbours, all belonging to S. The four positions translate back to distinct grid vertices surrounding the centre (x-1,y-1). Their coordinate bounds put this centre inside the grid, each of the four vertices is adjacent to it, and every neighbour of the centre is one of these four. Independence of S is not required for this implication.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
