using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnSequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnSequence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A characteristic-zero scalar field realizes both reciprocal branches and a bilateral recurrence for the mixed column determinant.",
        H("A Scalar Model for the Column Sequence"),
        Blocks(
            Node("cigler-motzkin-column-sequence-model", "The reciprocal-branch scalar model", "scalar_model",
                "For every nonnegative k and m there is a field K of characteristic zero and an injective ring homomorphism phi from the integer polynomial ring in t to K. There are a nonzero alpha and a primitive root zeta of order 2(k+1), with phi(t) = alpha + alpha inverse and alpha - alpha inverse nonzero. Every r_i = phi(t) + zeta^(i+1) + (zeta^(i+1)) inverse for i below k is nonzero. Put w_i = -zeta^(i+1). There are scalars a_i and b_i such that (-1)^n p_n(r_i) = a_i w_i^n + b_i w_i^(-n) and (-1)^(n+1)b_n(r_i) = a_i w_i^(-n-1) + b_i w_i^(n+1) for all nonnegative n, where p_n and b_n are the specialized orthogonal and backward polynomials with coefficients mapped by phi. There are also an invertible formal series z(y) of constant coefficient alpha and formal series A(y) and B(y) with (-1)^n p_n(y) = A z^n + B z^(-n) and (-1)^(n+1)b_n(y) = A z^(-n-1) + B z^(n+1). For the first m columns rescale z, A and B by y becoming j y, with j from zero to m minus one; for the remaining k columns use the constant series w_i, a_i and b_i. Denote these triples by u_j, aa_j and bb_j. For every integer n let v(n) be the coefficient of y^binom(m,2) in the determinant with entry aa_j u_j^(n+r) + bb_j u_j^(-n-r) in row r and column j below m+k. If Q is the image under phi of the specified column denominator, then the sum of Q_d v(n-d), for d from zero through the degree of Q, is zero for every integer n.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
