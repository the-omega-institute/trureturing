using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube231LargePrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed boundary data for two consecutive inverse images determine additional small entries.",
        H("Low Entries in the Forced Prefix"),
        Blocks(
            Node("fundamental-bijection-thetacube231largeprefix-forced-low-prefix", "Four forced small entries", "forced_low_prefix",
                "Let p and q be permutations of size n at least eleven with p avoiding 231, q the inverse image of p, and the second inverse image of q equal to p. Suppose p starts with n, one, n minus two, two and ends with n minus one, while q has n minus two, n minus one, n, one at positions zero, n minus four, n minus two, n minus one. Then q has four and three at positions one and three, and p has four and three at positions four and five.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
