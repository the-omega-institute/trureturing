using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215PieceEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215PieceEnumeration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decreasing subset of original sites and an ordered list of pure histories enumerate the original pieces.",
        H("Enumeration of Original Pieces"),
        Blocks(
            Node("weak-ascent-weakascent215pieceenumeration-original-piece-enumeration", "Original pieces as subsets and lists", "original_piece_enumeration",
                "For every gap g, original pieces have strictly decreasing cut sites and one more pure piece than cut sites. For either Boolean value of the old mark, the replay length equals the number of cut sites plus the sum of the pure piece lengths, and its expenditure equals the sum of their expenditures. There is a bijection from original pieces of gap g to pairs consisting of a subset S of the sites below g and an ordered list of cardinality S plus one pure histories; it sends the cut sites to S and preserves the ordered pure pieces.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
