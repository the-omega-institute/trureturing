using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class OneStepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/OneStep.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("One Step"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate one step to the stochastic ellipsoid construction.")),
            Node("claim-1", "log_le_sub_one_sub_sq", "log le sub one sub sq",
                "The scalar one-step inequality. For 1 ≤ M and 0 < v ≤ M, log v ≤ (v − 1) − (v − 1)² / (2 M). M is sharp: g v = (v−1) − (v−1)²/(2M) − log v has g' v = (v−1)(M−v)/(vM), which changes sign at v = M.", DescribeRole.Theorem),
            Node("claim-2", "trace_eq_sum_eigenvalues_real", "trace eq sum eigenvalues real",
                "trace of a real Hermitian matrix, with the RCLike.ofReal coercion discharged.", DescribeRole.Theorem),
            Node("claim-3", "spectral_real", "spectral real",
                "The spectral decomposition of a real Hermitian matrix, coercion discharged.", DescribeRole.Theorem),
            Node("claim-4", "det_one_add_eq_prod", "det one add eq prod",
                "det (1 + B) = ∏ (1 + λᵢ) for Hermitian B.", DescribeRole.Theorem),
            Node("claim-5", "trace_mul_self_eq_sum_sq", "trace mul self eq sum sq",
                "tr (B * B) = Σ λᵢ² for Hermitian B.", DescribeRole.Theorem),
            Node("claim-6", "trace_mul_self_eq_sum_sq_entries", "trace mul self eq sum sq entries",
                "tr (B * B) = Σᵢⱼ Bᵢⱼ² for Hermitian B: the Frobenius norm squared, entrywise.", DescribeRole.Theorem),
            Node("claim-7", "sum_sq_eigenvalues_eq_frobenius", "sum sq eigenvalues eq frobenius",
                "The Frobenius norm squared of a Hermitian matrix is the sum of squares of its eigenvalues.", DescribeRole.Theorem),
            Node("claim-8", "log_det_one_add_le", "log det one add le",
                "One-step inequality after congruence. For Hermitian B whose shifted eigenvalues 1 + λᵢ are positive and bounded above by M ≥ 1, log det (1 + B) ≤ tr B − (Σ λᵢ²)/(2M).", DescribeRole.Theorem),
            Node("claim-10", "log_det_add_le", "log det add le",
                "The one-step log-det inequality. S is any symmetric congruence factor with S A S = 1 (think S = A^{-1/2}); B = S H S is then A^{-1/2} H A^{-1/2}: log det (A + H) ≤ log det A + tr (A⁻¹ H) − ‖A^{-1/2} H A^{-1/2}‖_F² / (2M) where M ≥ 1 bounds the eigenvalues of A^{-1/2}(A+H)A^{-1/2} from above. This is the discrete replacement for Klartag's Lemma 3.3: summing it along the chain is the Riemann sum of −(1/2)∫ δ_s ds, with no Itô formula and no local-martingale argument.", DescribeRole.Theorem),
            Node("claim-11", "log_det_add_le_kappa", "log det add le kappa",
                "The paper's shape: with κ ≥ 1 bounding the eigenvalues of A^{-1/2}(A+H)A^{-1/2}, the quadratic gain is ‖A^{-1/2} H A^{-1/2}‖_F² / (2κ²).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
