using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuRankTwoSpectatorCompressionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cold cost and rank-two purity under normalized spectator compression.",
        H("Rank-two spectator compression"),
        Blocks(
            Paragraph(Text(
                "In Wu’s signed-spin setting, use occupation order (spectator, cold), ordinary traces, "
                + "and the cold jump J_c = Z ⊗ e with e = |0⟩⟨1|. Write Q = Tr_s(A)/2, C = I ⊗ Q, and H = A − C. "
                + "The cold quadratic is k(B) = c Re Tr(B²) + q Re Tr(B²P₀) − K Re Tr(B J_c B J_c†). "
                + "Here P₀ = J_c J_c†, P₁ = J_c† J_c, and k_* = c − (K − q)²/(4K) for K > 0.")),
            Entry("cold-projectors", "cold_projectors", "Cold occupation projections",
                "The two products of the signed jump with its adjoint are the lifted vacuum and occupied projections. Their sum is I."),
            Entry("positive-cold-marginal", "coldMarginal_posSemidef", "Positive cold marginal",
                "For every positive semidefinite A, the partial trace over the spectator is positive semidefinite, and scaling it by 1/2 gives a positive semidefinite Q."),
            Entry("lifted-trace-pairing", "trace_mul_liftCold", "Trace pairing with cold observables",
                "For arbitrary complex A and cold matrix R, Tr(A(I ⊗ R)) = Tr((Tr_s A)R)."),
            Entry("marginal-of-lift", "coldMarginal_liftCold", "Marginal of a lifted observable",
                "The normalized spectator partial trace of I ⊗ R is R."),
            Entry("positive-cold-lift", "liftCold_posSemidef", "Positive cold lift",
                "If R is positive semidefinite, then I ⊗ R is positive semidefinite."),
            Entry("zero-remainder-marginal", "partialTrace_remainder", "Zero partial trace of the remainder",
                "For arbitrary complex A, Tr_s H = 0, so the trace pairing of H with any lifted cold observable vanishes."),
            Entry("trace-remainder-square", "trace_remainder_sq", "Trace purity under compression",
                "For arbitrary complex A, Re Tr(H²) = Re Tr(A²) − 2 Re Tr(Q²). The two mixed traces vanish by the partial-trace pairing."),
            Entry("signed-cold-overlap", "trace_cold_overlap", "Exact signed cold overlap",
                "For every complex cold matrix Q and C = I ⊗ Q, Tr(C J_c C J_c†) = 2 Q₀₀ Q₁₁. The two spectator Z factors multiply to I."),
            Entry("cold-completed-square", "coldQuadratic_lift_eq", "Exact cold cost on the lifted marginal",
                "For Hermitian Q and K > 0, set δ = Re(Q₀₀ − Q₁₁). Then k(C) = k_* Re Tr(C²) "
                + "− (K + q²/K) Re det Q + (K/2)(δ + q Re Tr(Q)/K)². The determinant includes the squared modulus of the complex off-diagonal entry."),
            Entry("cold-lift-lower", "coldQuadratic_lift_lower", "Cold lift bound",
                "Dropping the nonnegative square gives k(C) ≥ k_* Re Tr(C²) − (K + q²/K)d/4 with d = 4 Re det Q."),
            Entry("cold-compression-lower", "coldQuadratic_compression_lower", "Cold compression bound",
                "For positive semidefinite A and K > 0, the cold lift bound applies to Q = Tr_s(A)/2."),
            Entry("determinant-eigenvalues", "det_re_eq_eigenvalue_product", "Cold determinant from the eigenvalues",
                "For Hermitian Q, Re det Q equals the product of its two real eigenvalues."),
            Entry("rank-two-purity", "rankTwo_purity", "Exact rank-two remainder purity",
                "For Hermitian A with Re Tr(A) = a + b and Re Tr(A²) = a² + b², the identity is "
                + "Re Tr(H²) = (a − b)²/2 + 4 Re det Q. The two moments give the rank-two formula and include the case b = 0."),
            Entry("cold-imbalance-witness", "exists_cold_matrix_imbalance", "Realizing every feasible cold imbalance",
                "For ν ≥ μ ≥ 0, every δ in [−(ν − μ), ν − μ] is realized by a positive semidefinite Q "
                + "with trace ν + μ and determinant νμ. Choose diagonal entries (ν + μ ± δ)/2 and both off-diagonal entries √((ν − μ)² − δ²)/2."),
            Entry("attained-cold-minimum", "coldQuadratic_minimum", "Sharp cold cost with attainment",
                "For K > 0 and fixed cold eigenvalues ν ≥ μ ≥ 0, put t = −q(ν + μ)/K and "
                + "δ = max(−(ν − μ), min(ν − μ, t)). The attained minimum over all positive semidefinite complex cold matrices with these eigenvalues is "
                + "2k_*(ν² + μ²) − (K + q²/K)νμ + (K/2)(δ − t)². The imbalance witness attains this value. "
                + "The last term vanishes when t lies in the spectral interval, and the same formula applies when ν = μ."),
            Entry("cold-remainder-split", "coldQuadratic_split", "Exact splitting of the signed cold cost",
                "For arbitrary complex A, k(A) = k(C) + k(H). Multiplication by P₀ and conjugation by J_c or J_c† preserve the lifted cold algebra, so all mixed traces vanish."),
            Entry("complex-cold-overlap-bound", "cold_overlap_le", "Complex remainder overlap on the actual cold jump",
                "For Hermitian H, put X = Re Tr(H²P₀) and Y = Re Tr(H²P₁). These are the squared Hilbert–Schmidt norms "
                + "of H J_c and H J_c†, respectively. Complex trace Cauchy–Schwarz gives |Re Tr(H J_c H J_c†)| ≤ √X √Y."),
            Entry("cold-remainder-lower", "coldQuadratic_remainder_lower", "Cold quadratic bound on the remainder",
                "For Hermitian H and K > 0, the signed overlap bound and a sum of two real squares give k(H) ≥ (k_* − K/4) Re Tr(H²)."),
            Entry("rank-two-determinant-bounds", "rankTwo_det_bounds", "Range of the determinant correction",
                "If A is positive semidefinite and Re Tr(A) = a + b, then 0 ≤ d ≤ (a² + b² − (a − b)²/2)/2."),
            Entry("rank-two-frame-moments", "rankTwo_frame_moments", "Moments in a complex orthonormal frame",
                "For U†U = I and a,b ≥ 0, A = U diag(0,0,b,a) U† is positive semidefinite and has ordinary moments "
                + "Re Tr(A) = a + b and Re Tr(A²) = a² + b²."),
            Entry("rank-two-joint-bound", "rankTwo_joint_lower", "Joint bound on the same matrix",
                "For positive semidefinite A with these moments, let ℓ = (a − b)²/2 and assume E_s ≥ Re Tr(H²). "
                + "For K > 0, the signed cold cost then satisfies E_s + k(A) ≥ "
                + "k_*(a² + b²) + (1 − K/4)ℓ + (1 − (2K + q²/K)/4)d."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
