using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube312SuffixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Suffix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance and a cyclic successor determine two additional suffix entries.",
        H("The Pair before the Terminal Configuration"),
        Blocks(
            Node("fundamental-bijection-thetacube312suffix-terminal-pair-positions", "Two forced suffix entries", "terminal_pair_positions",
                "For a 312-avoiding permutation of size n at least seven ending with n minus one, two, n, one and having cyclic successor n minus three for the letter three, the entries at positions n minus six and n minus five are three and n minus two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
