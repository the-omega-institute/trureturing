using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped2"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "norm_inv_apply_le", "norm inv apply le",
                "‖A⁻¹ y‖ ≤ ‖y‖ / m from the quadratic-form lower bound. With x = A⁻¹ y, m‖x‖² ≤ ⟪x, A x⟫ = ⟪x, y⟫ ≤ ‖x‖‖y‖.", DescribeRole.Theorem),
            Node("claim-2", "norm_matToUT_sq", "norm mat To UT sq",
                "The Frobenius norm of a symmetric matrix, in the model's currency: ‖matToUT M‖² = ∑_{i,j} M_ij².", DescribeRole.Theorem),
            Node("claim-3", "norm_apply_single_sq", "norm apply single sq",
                "‖M eⱼ‖² = ∑ᵢ Mᵢⱼ².", DescribeRole.Theorem),
            Node("claim-4", "sum_sq_eq_sum_norm_sq", "sum sq eq sum norm sq",
                "The Frobenius norm as a sum of column norms — the shape the bound on V needs.", DescribeRole.Theorem),
            Node("claim-5", "norm_matToUT_inv_le", "norm mat To UT inv le",
                "‖matToUT A⁻¹‖ ≤ √(dim) / m. The Frobenius norm of the inverse is bounded column by column by norm_inv_apply_le, and matToUT is a Frobenius isometry.", DescribeRole.Theorem),
            Node("claim-6", "norm_stoppedV_le", "norm stopped V le",
                "The bound on V — ‖π_k(A_k⁻¹)‖ ≤ √(dim)/m, for the stopped chain, everywhere.", DescribeRole.Theorem),
            Node("claim-7", "stoppedErr_mid_le", "stopped Err mid le",
                "The integrand bound at the one disagreeing step. At k = τ − 1 the stopped error is c‖π_kξ_k‖² − ⟪V k, ξ k⟫, and both terms are controlled by ‖ξ k ω‖: the projection is a contraction, and ‖V k‖ ≤ √(dim)/m by §1. This is the integrand whose integral the drift's hbd needs, and it is the only place the stopped error is not ChainWiring.chainErr.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
