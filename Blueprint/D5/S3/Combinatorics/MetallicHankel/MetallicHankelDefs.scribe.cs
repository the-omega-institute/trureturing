using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The q-metallic quadratic equation defines integral power series and their shifted Hankel determinants.",
        H("q-Metallic Series and Shifted Hankel Determinants"),
        Blocks(
            Node("metallic-hankel-defs-linear-coeff", "The linear coefficient of the quadratic equation", "linearCoeff",
                "For a nonnegative integer n, put [n]_q = 1 + q + ... + q^{n-1}, with the empty sum zero. The integral formal power series B_n(q) is (1 + q^n)(1 - q) - q[n]_q.", DescribeRole.Definition),
            Node("metallic-hankel-defs-is-metallic", "The q-metallic equation", "IsMetallic",
                "An integral formal power series Phi is q-metallic with parameter n when its constant coefficient is one and q Phi^2 + B_n(q) Phi = 1, where B_n(q) = (1 + q^n)(1 - q) - q[n]_q.", DescribeRole.Definition),
            Node("metallic-hankel-defs-shifted-hankel", "Shifted Hankel determinants", "shiftedHankel",
                "For an integral formal power series Phi(q) = sum_{r >= 0} f_r q^r and nonnegative integers ell and j, Delta_j^{(ell)} is the determinant of the j by j matrix with entry f_{ell+a+b} in row a and column b, with indices starting at zero. The empty determinant Delta_0^{(ell)} is one.", DescribeRole.Definition),
            Node("metallic-hankel-defs-claim", "The periodicity and value assertion", "claim",
                "For every integer n at least two, an integral q-metallic series Phi exists. For every integral q-metallic series with that parameter and every nonnegative integer j, Delta_{j+2n(n+1)}^{(n+2)} = (-1)^n Delta_j^{(n+2)}, and Delta_j^{(n+2)} belongs to {-2, -1, 0, 1, 2}. This is part 1 of Conjecture E of Han and Pedon.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
