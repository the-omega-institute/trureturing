using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance of 132 through successive iterates has a cubic quasipolynomial count followed by linear and constant counts.",
        H("Enumeration of Iterated 132-Avoiders"),
        Blocks(
            Node("fundamental-bijection-thetaiterate-result", "The counts through every iteration depth", "result",
                "Let t(n,k) count the permutations of size n whose iterates from zero through k under the fundamental bijection all avoid 132. For n at least two, t(n,2) is m cubed + 3m squared + 2m - 1 when n = 3m, m cubed + 4m squared + 4m when n = 3m + 1, and m cubed + 5m squared + 7m + 2 when n = 3m + 2. For n at least three, t(n,3) = 3n - 4, t(n,4) = 2n - 1, t(n,5) = n + 2, and t(n,k) = 5 for every k at least six.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
