using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215WeightedRenewalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215WeightedRenewal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure prefixes and their terminal old sites give a weighted recurrence for full histories.",
        H("Weighted Renewal Counts"),
        Blocks(
            Node("weak-ascent-weakascent215weightedrenewal-weighted-renewal", "The finite weighted renewal recurrence", "weighted_renewal",
                "Fix a Boolean e and nonnegative integers b and d. The initial stack is a singleton true mark when e is true and is empty otherwise, with initial budget b and mode e. The pure histories h of length at most d and expenditure less than b form a finite collection. The number of full histories of length d + 1 from this initial state equals the number of pure histories of that length and expenditure less than b, plus a sum over this collection. For a prefix h, put r = b minus its expenditure and t = d minus its length, let a be its terminal old-entry count plus one when e is true and unchanged otherwise, and let m be one when its final mode is true and zero otherwise. Its contribution is (a minus m) times the number of full histories of length t from the empty stack with budget r and false mode, plus m times the number from the singleton true stack with budget r + 1 and true mode.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
