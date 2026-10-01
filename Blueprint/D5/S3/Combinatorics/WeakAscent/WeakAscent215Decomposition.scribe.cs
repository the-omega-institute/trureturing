using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215DecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Decomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first record splits a nonempty pure history into a gap, descending sites and smaller pure histories.",
        H("Decomposition at the First Record"),
        Blocks(
            Node("weak-ascent-weakascent215decomposition-first-record-decomposition", "First-record decomposition and its series identity", "first_record_decomposition",
                "Nonempty pure histories are in bijection with triples consisting of a nonnegative gap g, a subset S of the sites from zero through g minus one, and an ordered list of cardinality S plus one pure histories. The sites occur in decreasing order. Reconstruction starts with a record of gap g and then replays the corresponding pieces above an old entry. Its length is one plus the cardinality of S plus the sum of the piece lengths, and its expenditure is g plus the sum of the piece expenditures. If P(z,x) counts pure histories by expenditure z and length x, then P + z(1 + xP) = 1 + xP + z(1 + xP)P.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
