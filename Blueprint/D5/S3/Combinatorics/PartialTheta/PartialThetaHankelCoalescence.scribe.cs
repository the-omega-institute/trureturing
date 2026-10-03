using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelCoalescenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coalescing alternant variables at one yields a binomial determinant, and a staircase specialization evaluates it.",
        H("Coalescence and the Staircase Pascal Determinant"),
        Blocks(
            Node("partial-theta-hankel-coalescence-staircase-det", "The staircase determinant", "staircase_det",
                "For all nonnegative integers m and n, form a square integer matrix of size m + n + 1, with row and column indices beginning at zero. In row i below m its entry in column j is one when m - i is at most j and zero otherwise. In row i at least m its entry is binom(j, i - m). The determinant is (-1)^{binom(m + 1, 2)}. Finite differences of the binomial rows give a Pascal determinant of value one, while the staircase rows contribute the stated sign.", DescribeRole.Theorem),
            Node("partial-theta-hankel-coalescence-coalescence", "Evaluation of a divided alternant at one", "coalescence",
                "For nonnegative integers m and c, choose any m by (m + c) matrix T with integer entries and any integer polynomial B in variables x_0 through x_{c-1}. Form the square matrix A of size m + c whose first m rows are T and whose row m + k has entry x_k^j in column j. Suppose det A equals product over 0 at most u less than v below c of (x_v - x_u), multiplied by B. Then B(1, through 1) equals the determinant of the integer matrix with the same first m rows T and with entry binom(j, k) in row m + k and column j. Expansion at x_k = 1 identifies the first alternating homogeneous component with this binomial determinant; the identity also includes c = 0.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
