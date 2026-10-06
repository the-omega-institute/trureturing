using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelLowestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse permutation gives the unique lowest-degree nonzero term of the backward-shifted Hankel determinant.",
        H("The Lowest Term of the Shifted Hankel Determinant"),
        Blocks(
            Node("partial-theta-hankel-lowest-lowest-term", "The first nonzero coefficient", "lowest_term",
                "For every pair of nonnegative integers m and n, every coefficient of D_{-m,n+m+1}(q) below degree (m + n + 1) binom(n, 2) vanishes, and the coefficient at that degree is (-1)^{binom(m + n + 1, 2)}. A determinant term can be nonzero only when its permutation sends each index i to an index j with i + j at least m. Among these permutations, the full reversal uniquely minimizes the sum of binom(i + j - m, 2). Its sign is the displayed coefficient.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
