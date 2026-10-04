using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuGaussianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian polynomials satisfy support, complementary-index, and rim identities.",
        H("Gaussian Recurrences and Symmetry"),
        Blocks(
            Node("li-uncu-gaussian-gauss-zero-of-lt", "Vanishing above the upper index", "gauss_zero_of_lt",
                "For nonnegative integers a and b with a less than b, G(a,b) = 0.", DescribeRole.Theorem),
            Node("li-uncu-gaussian-gauss-pascal-dual", "The second Gaussian recurrence", "gauss_pascal_dual",
                "For all nonnegative integers a and b, G(a+1,b+1) = q^(b+1) G(a,b+1) + G(a,b).", DescribeRole.Theorem),
            Node("li-uncu-gaussian-gauss-symmetry", "Complementary lower indices", "gauss_symmetry",
                "For nonnegative integers a and b with b at most a, G(a,b) = G(a,a-b).", DescribeRole.Theorem),
            Node("li-uncu-gaussian-gauss-hook", "The rim identity", "gauss_hook",
                "For nonnegative integers a and b with b at most a, (1 - q^(a-b)) G(a,b) = (1 - q^a) G(a-1,b). Subtraction of natural indices is truncated at zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
