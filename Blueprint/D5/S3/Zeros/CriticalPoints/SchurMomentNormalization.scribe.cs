using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class SchurMomentNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/SchurMomentNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization of nonzero spectral data and exact transfer between Schur diagonals and reciprocal critical points.",
        H("Spectral moment normalization and transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-normalized-weights"),
                DeclarationHandle.Create(Prefix + "normalized_weights"),
                H("Positive normalized spectral weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty finite family of nonzero complex mu_k and p>0, there exist N>0, positive rho_k and unit phases v_k with mu_k=v_k N rho_k, sum_k rho_k^p=1, N^p=sum_k norm(mu_k)^p, and sum_k conj(v_k) rho_k^(p−1) mu_k=N. Thus the same normalized data serve both the left boundary and interpolation center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-diagonal-root-moment"),
                DeclarationHandle.Create(Prefix + "schur_roots_moment"),
                H("The diagonal moment in a unitary Schur basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If Q is unitary and Q* A Q is upper triangular, the sum of norm-to-p over every characteristic root of A, counted with multiplicity, equals the sum of norm-to-p over the diagonal entries of Q* A Q. The identity holds for every real p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-reciprocal-root-moment"),
                DeclarationHandle.Create(Prefix + "reciprocal_moment"),
                H("The reciprocal critical-point moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite family of nonzero complex z_j and every real p, the sum of norm(w)^(−p) over the derivative roots of the reused polynomial P is exactly the p-th norm moment of the characteristic roots of D(I+J), where D has diagonal entries 1/z_j. This directly reuses the multiplicity-preserving reciprocal-root identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-sandwich-charpoly"),
                DeclarationHandle.Create(Prefix + "A_charpoly"),
                H("The characteristic polynomial of the Hermitian sandwich"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>0 and arbitrary complex diagonal b, define A=H(n,1/2) diag(b) H(n,1/2). Its characteristic polynomial equals that of diag(b)(I+J). If all b_j are nonzero, A is invertible; consequently every diagonal entry in a unitary upper-triangular Schur form is nonzero."))),
                DescribeRole.Theorem))));
}
