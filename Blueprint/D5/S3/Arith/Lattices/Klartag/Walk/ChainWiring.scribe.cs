using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainWiringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Wiring"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain wiring to the stochastic ellipsoid construction.")),
            Node("claim-2", "qUT", "q UT",
                "The constraint vector of a lattice point: the coordinates of x ⊗ x in the model.", DescribeRole.Definition),
            Node("claim-3", "symMat_qUT", "sym Mat q UT",
                "q x really is x ⊗ x.", DescribeRole.Theorem),
            Node("claim-4", "inner_qUT_eq_quad", "inner q UT eq quad",
                "⟪A, q x⟫ is the quadratic form. So Chain.kSet q W is the set of matrices whose ellipsoid E_A = {v | ⟪A v, v⟫ < 1} (Klartag eq. 9) misses the window, and Chain.freeSub q C is his F_A (eq. 13).", DescribeRole.Theorem),
            Node("claim-5", "inner_qUT", "inner q UT",
                "Non-negative correlation — hinge 1's ⟪x ⊗ x, y ⊗ y⟫ = (x ⬝ᵥ y)², the hypothesis Chain.lift_mem_kSet runs on.", DescribeRole.Theorem),
            Node("claim-8", "logDet", "log Det",
                "log det of a point of the model.", DescribeRole.Definition),
            Node("claim-9", "liftCost", "lift Cost",
                "err: the log-det cost of the correction at one step — the entire discretisation error of the chain.", DescribeRole.Definition),
            Node("claim-10", "preState", "pre State",
                "The chain's stepped matrix A'_{k+1} before the correction.", DescribeRole.Definition),
            Node("claim-11", "chainErr", "chain Err",
                "The chain's err k.", DescribeRole.Definition),
            Node("claim-12", "logDet_chain_succ", "log Det chain succ",
                "The step's log-determinant splits as the Gaussian part plus the error.", DescribeRole.Theorem),
            Node("claim-13", "measurableSet_active_eq", "measurable Set active eq",
                "The active set is a measurable Finset-valued random variable, fibre by fibre.", DescribeRole.Theorem),
            Node("claim-14", "measurable_of_active", "measurable of active",
                "Any real function of the active set is a measurable random variable. The active set takes finitely many values (Finset.powerset W), so the composition is a finite sum of indicators.", DescribeRole.Theorem),
            Node("claim-15", "measurable_freeDim", "measurable free Dim",
                "N_k = dim F(C_k) is measurable.", DescribeRole.Theorem),
            Node("claim-17", "integrable_logDet_of_bounds", "integrable log Det of bounds",
                "intD from a two-sided bound on the determinant. The lower bound is Klartag eq. (32), det A_t ≥ c_L, from Minkowski's first theorem (det_ge_of_volume_le below); the upper bound is the good event of Corollary 3.2 (H5).", DescribeRole.Theorem),
            Node("claim-18", "quadForm", "quad Form",
                "The quadratic form of a matrix, Q_M(v) = ⟪M v, v⟫.", DescribeRole.Definition),
            Node("claim-21", "inner_lift_sub", "inner lift sub",
                "The correction's cost carries no Frobenius norm. With q i = x_i ⊗ x_i, ⟪B, Δ⟫ = ∑_i λ_i · ⟪B x_i, x_i⟫, so the concavity bound on the log-determinant reads ∑_i λ_i ⟪(A')⁻¹ x_i, x_i⟫ ≤ λ_min(A')⁻¹ ∑_i λ_i |x_i|² — one factor of √n cheaper than ‖(A')⁻¹‖_F · ‖Δ‖_F, which is what the Frobenius projection would force.", DescribeRole.Theorem),
            Node("claim-22", "coeff_le", "coeff le",
                "Each coefficient is bounded by the step's own increment against that constraint. This is what makes the overshoot O(√h) rather than O(n√h): 1 - ⟪A + B, q i⟫ ≤ -⟪B, q i⟫ because A already satisfies the constraint.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
