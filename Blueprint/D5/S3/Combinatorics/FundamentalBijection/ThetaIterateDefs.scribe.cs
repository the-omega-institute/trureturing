using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The avoidance layers count permutations whose initial orbit segments avoid a fixed pattern.",
        H("Iterated Pattern Avoidance and Its Counts"),
        Blocks(
            Node("fundamental-bijection-thetaiteratedefs-iterateavoiders", "Avoidance through an iteration depth", "iterateAvoiders",
                "The layer of size n and depth k consists of permutations of one through n whose fundamental images at every iteration index from zero through k avoid the pattern sigma.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiteratedefs-quadcount", "A cubic quasipolynomial", "quadCount",
                "Write n = 3m + r with r zero, one, or two. The count is m cubed + 3m squared + 2m - 1 for r zero, m cubed + 4m squared + 4m for r one, and m cubed + 5m squared + 7m + 2 for r two, with subtraction in the nonnegative integers.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiteratedefs-claim", "The proposed counts for 132-avoidance", "claim",
                "The second-layer count is the cubic quasipolynomial for every size at least two. For every size n at least three, the counts at depths three, four, and five are 3n - 4, 2n - 1, and n + 2 respectively, and the count at every depth at least six is five.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
