using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StepInputs2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Step Inputs2"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate step inputs2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "opNorm_le_frobenius", "op Norm le frobenius",
                "The operator norm is at most the Frobenius norm, row by row by Cauchy–Schwarz. Mathlib has the two norms (Matrix.toEuclideanCLM, Matrix.frobenius_norm) but not this comparison in a form free of the scoped Matrix.Norms instances.", DescribeRole.Theorem),
            Node("claim-2", "opNorm_symMat_le_norm", "op Norm sym Mat le norm",
                "In the model of R^{n×n}_sym, the Frobenius norm of symMat x *is* the Euclidean norm of the coordinate vector x (Increments.sum_symMat_mul_eq_inner), so the operator norm of the matrix is at most ‖x‖.", DescribeRole.Theorem),
            Node("claim-3", "opNorm_symMat_starProjection_le", "op Norm sym Mat star Projection le",
                "The per-step bound in the currency oneStep_of_good consumes: the orthogonal projection contracts the Euclidean norm, so the operator norm of the projected increment is at most the norm of the increment.", DescribeRole.Theorem),
            Node("claim-4", "measureReal_abs_ge_le", "measure Real abs ge le",
                "Two-sided Gaussian tail.", DescribeRole.Theorem),
            Node("claim-5", "measureReal_norm_ge_le", "measure Real norm ge le",
                "The Euclidean-norm tail by a coordinate union bound. No independence is used: the coordinates only have to be marginally N(0, v).", DescribeRole.Theorem),
            Node("claim-6", "stepGood", "step Good",
                "The set on which every step has a small increment. This is the second half of the good event: GoodEvent.goodEvent controls the *accumulated* sum, this controls each single step, and GoodEvent.oneStep_of_good needs both.", DescribeRole.Definition),
            Node("claim-7", "measureReal_compl_stepGood_le", "measure Real compl step Good le",
                "The union bound over the N steps. Cost N · d · 2 · exp(−η²/(2 d v)).", DescribeRole.Theorem),
            Node("claim-9", "condExp_inner_eq_zero", "cond Exp inner eq zero",
                "H2 — the centred increment kills the middle term of the one-step inequality.", DescribeRole.Theorem),
            Node("claim-10", "sum_inner_starProjection", "sum inner star Projection",
                "The trace of an orthogonal projection is the dimension of its range, in the elementary ∑_p ⟪b p, π (b p)⟫ form. Mathlib has LinearMap.IsProj.trace but not this, and not the bridge from LinearMap.trace to an orthonormal-basis sum.", DescribeRole.Theorem),
            Node("claim-12", "norm_starProjection_sq_eq", "norm star Projection sq eq",
                "The quadratic form of an orthogonal projection, in coordinates.", DescribeRole.Theorem),
            Node("claim-13", "condExp_quadForm", "cond Exp quad Form",
                "The conditional expectation of a quadratic form in the increment with ℱ-measurable coefficients.", DescribeRole.Theorem),
            Node("claim-16", "integral_coord_eq_zero", "integral coord eq zero",
                "The increment's coordinates are centred.", DescribeRole.Theorem),
            Node("claim-17", "integral_coord_mul", "integral coord mul",
                "The covariance of the increment's coordinates.", DescribeRole.Theorem),
            Node("claim-30", "log_det_step_unconj", "log det step unconj",
                "The one-step bound with the unconjugated quadratic gain. GoodEvent.oneStep_of_good produces -‖S H S‖²_F / (2(1+δ)²); the conversion turns it into -‖H‖²_F / (2 M² (1+δ)²), which is the shape whose conditional expectation H3 computes.", DescribeRole.Theorem),
            Node("claim-31", "inner_starProjection_swap", "inner star Projection swap",
                "⟪u, π x⟫ = ⟪π u, x⟫: the form in which the chain's middle term ⟪A_k⁻¹, π_k ξ_k⟫ = ⟪π_k A_k⁻¹, ξ_k⟫ is fed to H2, whose V is then π_k A_k⁻¹.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
