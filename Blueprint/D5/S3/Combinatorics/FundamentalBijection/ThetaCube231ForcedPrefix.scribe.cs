using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube231ForcedPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube231ForcedPrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A predecessor of one and the terminal value determine a decreasing prefix.",
        H("The High Prefix before One"),
        Blocks(
            Node("fundamental-bijection-thetacube231forcedprefix-forced-high-prefix", "A forced decreasing prefix", "forced_high_prefix",
                "For a 231-avoiding permutation of size n ending with c, if one occurs at a position t strictly between zero and n minus one and is preceded by c plus one, then its first t letters are n, n minus one, down to c plus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
