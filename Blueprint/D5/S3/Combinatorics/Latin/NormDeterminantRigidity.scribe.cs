using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class NormDeterminantRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/NormDeterminantRigidity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/mazhang2026factorperfection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex n-by-n factors of squared Frobenius norm n with a unitary product are unitary.",
        H("Norm–determinant rigidity of unitary products"),
        Blocks(
            Describe.Lean(DescribeId.Create("norm-determinant-rigidity"),
                DeclarationHandle.Create(Prefix + "norm_det_le_one_and_rigid"),
                H("Determinant bound and its equality case"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let M be a complex n×n matrix whose squared Frobenius norm "
                    + "∑ᵢ∑ⱼ‖M(i,j)‖² equals n. Then ‖det M‖ ≤ 1, and ‖det M‖ = 1 implies that M is "
                    + "unitary. The Hermitian matrix MᴴM is positive semidefinite with eigenvalues "
                    + "λ₁,…,λₙ ≥ 0; its trace gives ∑λᵢ = n and its determinant gives "
                    + "∏λᵢ = ‖det M‖². From λ ≤ exp(λ−1) one gets ∏λᵢ ≤ exp(∑(λᵢ−1)) = 1. If "
                    + "‖det M‖ = 1, every λᵢ is positive, and a λⱼ ≠ 1 would make the inequality "
                    + "strict, so every eigenvalue is 1 and the spectral theorem gives MᴴM = 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unitary-product-factors"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Factors of a unitary product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every size n, including n = 0, and every finite list of complex n×n "
                    + "matrices, each of squared Frobenius norm n, if the product of the list is "
                    + "unitary then every matrix in the list is unitary. The determinant norm of "
                    + "a unitary matrix is 1 and determinant norms are multiplicative; since each "
                    + "factor has determinant norm at most 1, a product of these norms equal to 1 "
                    + "forces each of them to be 1, and the equality case above applies to every "
                    + "factor."))),
                DescribeRole.Theorem))));
}
