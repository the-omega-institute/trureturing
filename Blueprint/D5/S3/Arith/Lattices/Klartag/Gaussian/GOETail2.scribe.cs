using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GOETail2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("GOETail2"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate goetail2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "hasSubgaussianMGF_of_hasLaw_gaussianReal", "has Subgaussian MGF of has Law gaussian Real",
                "A real random variable whose law is N(0, v) has a sub-Gaussian MGF with parameter v. Mathlib has mgf_gaussianReal and integrable_exp_mul_gaussianReal but no bridge to HasSubgaussianMGF, which occurs in no file other than Probability/Moments/SubGaussian.lean.", DescribeRole.Theorem),
            Node("claim-2", "hasSubgaussianMGF_of_map_gaussianReal", "has Subgaussian MGF of map gaussian Real",
                "A nondegenerate Gaussian map equality also certifies a.e. measurability: a nonmeasurable map has zero pushforward, whereas every Gaussian law is a probability measure.", DescribeRole.Theorem),
            Node("claim-3", "dotProduct_mulVec_comm", "dot Product mul Vec comm",
                "The bilinear form of a symmetric matrix is symmetric.", DescribeRole.Theorem),
            Node("claim-4", "inner_toEuclideanCLM_symm", "inner to Euclidean CLM symm",
                "toEuclideanCLM of a symmetric real matrix is self-adjoint, in the elementary form D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.opNorm_le_of_net consumes.", DescribeRole.Theorem),
            Node("claim-5", "isSymm_add_transpose", "is Symm add transpose",
                "B + Bᵀ is symmetric.", DescribeRole.Theorem),
            Node("claim-6", "quadForm", "quad Form",
                "The quadratic form of the symmetrised matrix, as a linear form in the independent entries of B.", DescribeRole.Definition),
            Node("claim-7", "inner_symmetrized", "inner symmetrized",
                "Step 3a. The quadratic form of B + Bᵀ is a sum over the *full* product Fin n × Fin n of the independent entries of B, with coefficients 2 x_i x_j. No i ≤ j filter and no Prod.swap reindexing: the only reindexing is one Finset.sum_comm.", DescribeRole.Theorem),
            Node("claim-8", "sum_sq_coord_eq_one", "sum sq coord eq one",
                "A unit vector of EuclideanSpace ℝ (Fin n) has coordinate squares summing to 1.", DescribeRole.Theorem),
            Node("claim-9", "hasSubgaussianMGF_quadForm", "has Subgaussian MGF quad Form",
                "Step 3c. For a unit vector x, the linear form ∑ p, (2 x_{p.1} x_{p.2}) B_{p.1 p.2} in the independent entries of B is sub-Gaussian with parameter 4c. The coefficient bound is D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.sum_sq_coeff_le; the closure properties are HasSubgaussianMGF.const_mul and .sum_of_iIndepFun, and the parameter is relaxed by D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.hasSubgaussianMGF_mono.", DescribeRole.Theorem),
            Node("claim-10", "opNormTail_symmetrized", "op Norm Tail symmetrized",
                "The tail, with C = 12. Steps 4 (union bound over the ε = 1/4 net), 5 (the constant), 6 (assembly) and 8 (n = 0).", DescribeRole.Theorem),
            Node("claim-11", "gaussian_opNormTail", "gaussian op Norm Tail",
                "The Gaussian case at a general variance, which is the form the discrete chain of hinge 1 plugs into: its increment after time t is a standard Gaussian on R^{n×n}_sym scaled by √t, i.e. B + Bᵀ with the entries of B i.i.d. N(0, t/4).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
