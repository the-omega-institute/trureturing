using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class CiglerElevenMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/cigler2023catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Jacobi recurrence expresses odd Catalan power coefficients as moments of a monic orthonormal polynomial family.",
        H("The Catalan Power Moment Dictionary"),
        Blocks(
            Node("cigler-eleven-moments-dictionary", "Normalized orthogonality and Catalan moments", "moment_dictionary",
                "Specialize the boundary-weighted Motzkin orthogonal polynomials to interior weight two and boundary weight one. The resulting rational polynomials satisfy p_0 = 1, p_1 = X-1 and p_{j+2} = (X-2)p_{j+1}-p_j. There exists a rational linear functional L on rational polynomials such that L(p_a p_b) is one when a equals b and zero otherwise, and L(X^t p_k) = C_{2k+1,t-k} for all nonnegative integers t and k. This includes the zero moments when t is less than k. The Jacobi operator acts on sequences by (Jv)_0 = v_0+v_1 and (Jv)_{j+1} = v_j+2v_{j+1}+v_{j+2}; L(f) is the zeroth coordinate of f(J) applied to the zeroth unit vector. Its powers have coordinates binom(2t,t+k)-binom(2t,t+k+1), which satisfy the two-step Pascal recurrence and identify the Catalan coefficients.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
