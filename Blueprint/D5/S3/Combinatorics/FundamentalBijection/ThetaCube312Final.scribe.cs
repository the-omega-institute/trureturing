using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube312FinalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Final.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The specified terminal configuration cannot return after three inverse applications.",
        H("Incompatible Terminal Entries"),
        Blocks(
            Node("fundamental-bijection-thetacube312final-terminal-collision", "A terminal contradiction", "terminal_collision",
                "For size n at least seven, no permutation fixed by the third inverse iterate has n minus two, n minus one, two, n at positions n minus five through n minus two, while its inverse image starts with n, has n minus three at position two and two at position n minus two, and its second inverse image also starts with n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
