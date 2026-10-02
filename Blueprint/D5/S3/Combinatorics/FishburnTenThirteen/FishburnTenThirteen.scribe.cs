using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Fishburn avoidance classes have the same binomial-Catalan enumeration.",
        H("Enumeration of Two Fishburn Avoidance Classes"),
        Blocks(
            Node("fishburntenthirteen-result", "The common binomial-Catalan count", "result", "For every positive integer n, the number of Fishburn permutations of length n avoiding 2413 and 2431 equals the number avoiding 2431 and 3241, and both numbers equal the sum over k from one through n of the binomial coefficient choosing k minus one from n minus one multiplied by the Catalan number of index n minus k.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
