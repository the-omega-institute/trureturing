using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215PiecesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Pieces.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure histories and recursive cuts describe the pieces below a newly created record.",
        H("Pure Histories and Original Pieces"),
        Blocks(
            Node("weak-ascent-weakascent215pieces-purehistory", "Pure histories", "PureHistory",
                "A pure history is a list of pure steps admitting a run from the empty Boolean stack to some terminal stack.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pieces-originalpieces", "Recursive original pieces", "OriginalPieces",
                "For a nonnegative gap g, original pieces consist either of a final pure history or of a cut at a site s below g, a pure history preceding that cut, and original pieces with the smaller gap s.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pieces-originalpieces-replay", "Replaying original pieces", "replay",
                "For gap g and an old mark e, replay shifts the descent sites of the first pure history by g plus one when e is true and by g otherwise. A final piece ends there. A cut at site s appends a descent to s and continues by replaying the remaining pieces with old mark false.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pieces-originalpieces-sites", "The cut-site list", "sites",
                "The site list is empty for a final piece. A cut contributes its site followed by the sites of the remaining pieces, viewed as sites below the original gap.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215pieces-originalpieces-pieces", "The ordered pure pieces", "pieces",
                "The pure-piece list consists of the terminal history in the final case. At a cut it consists of the history preceding the cut followed by the pure pieces of the remaining collection.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
