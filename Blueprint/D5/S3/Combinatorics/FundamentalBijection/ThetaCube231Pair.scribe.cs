using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube231PairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Pair.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A terminal one after two inverse applications determines an adjacent pair in the original permutation.",
        H("A Consecutive Pair Forced by a Return"),
        Blocks(
            Node("fundamental-bijection-thetacube231pair-terminal-inverse-edge-forces-pair", "The pair before one", "terminal_inverse_edge_forces_pair",
                "For a permutation of size n greater than one starting with n and ending with c, if its second inverse image ends with one, then c is below n and c plus one occurs immediately before one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
