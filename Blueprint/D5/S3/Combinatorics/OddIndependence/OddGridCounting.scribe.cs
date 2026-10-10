using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OddIndependence;

internal sealed class OddGridCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OddIndependence/OddGridCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependencegrids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two layers of zero padding make every occupied position contribute to exactly nine three by three windows.",
        H("Ninefold counting of padded square-grid positions"),
        Blocks(
            Node("odd-grid-ninefold-count", "Every occupied position occurs nine times", "ninefold_count",
                "Let b be a Boolean array on pairs of natural numbers with all occupied positions in the coordinate range from 2 through n+1 in each direction. Sum the occupancy of b(i+r,j+c) over i,j from zero through n+1 and offsets r,c from zero through two. This integer sum is nine times the occupancy sum of b(x,y) over x,y from zero through n+1. For each of the nine offset pairs, shifting the two coordinate sums leaves their values unchanged: positions omitted at the lower ends and positions introduced at the upper ends are unoccupied. Equivalently, every occupied position lies in exactly three eligible windows in each coordinate direction, hence in nine windows altogether.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
