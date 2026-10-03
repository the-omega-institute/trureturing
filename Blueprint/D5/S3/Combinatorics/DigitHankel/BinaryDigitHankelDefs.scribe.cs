using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class BinaryDigitHankelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted binary digit sums define Hankel determinants whose nonvanishing indices at t = -2 are triples around the numbers ceil(2^(k+2)/3).",
        H("Weighted Binary Digit Sums and Hankel Determinants"),
        Blocks(
            Node("binary-digit-hankel-defs-digit-sum", "The weighted binary digit sum", "digitSum",
                "For a nonnegative integer u with binary expansion u = sum_j epsilon_j 2^j and an integer t, S(u,t) = sum_j epsilon_j t^j, where each epsilon_j is zero or one. The sum is finite, and S(0,t) = 0.", DescribeRole.Definition),
            Node("binary-digit-hankel-defs-hankel", "The binary digit Hankel determinant", "hankel",
                "For a nonnegative integer n and an integer t, H(n,t) is the determinant of the n by n integer matrix with entry S(i+j,t) in row i and column j, where i and j range from zero to n minus one. The determinant of the empty matrix is one.", DescribeRole.Definition),
            Node("binary-digit-hankel-defs-threshold", "The centers of the index triples", "threshold",
                "For every nonnegative integer k, n_k = ceil(2^(k+2)/3), equivalently the integer quotient (2^(k+2) + 2)/3. The sequence begins 2, 3, 6, 11, 22, 43.", DescribeRole.Definition),
            Node("binary-digit-hankel-defs-claim", "The nonvanishing equivalence at minus two", "claim",
                "For every integer n at least two, H(n,-2) is nonzero if and only if there is a nonnegative integer k such that n + 1 = n_k, n = n_k, or n = n_k + 1, with n_k = ceil(2^(k+2)/3). This is the case d = 2 of Conjecture 5.7 in Section 5.1 of Sobolewski and Ulas's paper.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
