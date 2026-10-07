using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class GoodEventDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Good Event"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate good event to the stochastic ellipsoid construction.")),
            Node("claim-1", "abs_eigenvalues_le_opNorm", "abs eigenvalues le op Norm",
                "Every eigenvalue of a Hermitian matrix is bounded in absolute value by the ℓ² operator norm. Mathlib has the eigenvector basis (Matrix.IsHermitian.mulVec_eigenvectorBasis) but not this bound.", DescribeRole.Theorem),
            Node("claim-2", "abs_inner_self_le_opNorm", "abs inner self le op Norm",
                "The quadratic form is controlled by the operator norm.", DescribeRole.Theorem),
            Node("claim-3", "posDef_of_inner_pos", "pos Def of inner pos",
                "Positive-definiteness read off the quadratic form on EuclideanSpace.", DescribeRole.Theorem),
            Node("claim-4", "opNorm_conj_le", "op Norm conj le",
                "Submultiplicativity of the ℓ² operator norm under congruence, obtained through toEuclideanCLM rather than through the scoped Matrix.Norms.L2Operator instances.", DescribeRole.Theorem),
            Node("claim-5", "posDef_one_add", "pos Def one add",
                "1 + B is positive definite as soon as ‖B‖_op < 1.", DescribeRole.Theorem),
            Node("claim-6", "isSymm_of_isHermitian", "is Symm of is Hermitian",
                "For real matrices, Hermitian is symmetric.", DescribeRole.Theorem),
            Node("claim-7", "lowerBound_of_opNorm_le", "lower Bound of op Norm le",
                "a₀·1 + G ⪰ (a₀ − ‖G‖)·1 in the quadratic-form sense: the shape the good event delivers, since A_k − a₀·Id is the accumulated increment.", DescribeRole.Theorem),
            Node("claim-8", "opNorm_sq_le_of_lowerBound", "op Norm sq le of lower Bound",
                "If A ⪰ m in the quadratic-form sense and S A S = 1 with S symmetric, then ‖S‖_op² ≤ 1/m. With S = A^{-1/2} this is ‖A^{-1/2}‖²_op = λ_min(A)⁻¹.", DescribeRole.Theorem),
            Node("claim-9", "oneStep_bounds_of_opNorm_le", "one Step bounds of op Norm le",
                "H5, eigenvalue half. If the conjugated increment B = S H S has ‖B‖_op ≤ δ < 1 then the two eigenvalue hypotheses of D5.S3.Arith.Lattices.Klartag.log_det_add_le_kappa hold with κ = 1 + δ.", DescribeRole.Theorem),
            Node("claim-10", "posDef_add_of_conj", "pos Def add of conj",
                "H5, cone half. A + H stays positive definite. The congruence S(A+H)S = 1 + S H S transports posDef_one_add back, using that S is invertible with S⁻¹ = A S = S A.", DescribeRole.Theorem),
            Node("claim-11", "log_det_step_le", "log det step le",
                "The composed one-step bound. On the good event (‖S H S‖_op ≤ δ < 1) the log-determinant obeys Klartag's Lemma 3.3 in discrete form with κ = 1 + δ, and A + H is still in the cone.", DescribeRole.Theorem),
            Node("claim-12", "oneStep_of_good", "one Step of good",
                "H5, end to end. From what the good event supplies — a lower bound m on A's quadratic form and an operator-norm bound η on the increment — the conjugated increment obeys ‖A^{-1/2} H A^{-1/2}‖_op ≤ η/m, so if η/m ≤ δ < 1 both halves of H5 hold and the one-step log-det inequality applies with κ = 1 + δ.", DescribeRole.Theorem),
            Node("claim-13", "goodEvent", "good Event",
                "The good event of Klartag's Proposition 3.4 (p. 16, eq. 43): the accumulated Gaussian part of A_N − a₀·Id has operator norm at most r.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
