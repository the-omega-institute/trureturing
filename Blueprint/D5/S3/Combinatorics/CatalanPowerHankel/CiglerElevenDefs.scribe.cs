using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class CiglerElevenDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/cigler2023catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd powers of the Catalan generating function determine shifted Hankel determinants with a conjectured closed form.",
        H("Shifted Hankel Determinants of Catalan Powers"),
        Blocks(
            Node("cigler-eleven-defs-coefficients", "The Catalan power coefficients", "catalanPowerCoeff",
                "For a nonnegative integer r and an integer j, define the rational number C_{r,j} to be r/(2j+r) times binom(2j+r,j) when j is nonnegative, and zero when j is negative. Division by zero gives zero. For positive r, these are the coefficients of the r-th power of the Catalan generating function c(x).", DescribeRole.Definition),
            Node("cigler-eleven-defs-hankel", "The shifted Hankel determinant", "shiftedHankel",
                "For a nonnegative integer r, an integer shift s and a nonnegative integer N, define D_{r,s}(N) as the determinant of the N by N matrix with entry C_{r,i+j+s} in row i and column j, where both indices range from zero through N minus one. The determinant of the empty matrix is one, and negative coefficient indices contribute zero.", DescribeRole.Definition),
            Node("cigler-eleven-defs-claim", "The odd-power determinant formula", "claim",
                "Conjecture 11 asserts that for every integer k at least one, every integer m from zero through k+1, and every nonnegative integer n, D_{2k+1,m-k+1}((2k+1)n+k) = (-1)^(kn+binom(k,2)) (2k+1)^m (n+1)^m. The shift m-k+1 is an integer and may be negative.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
