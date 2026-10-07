using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GOETailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("GOETail"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate goetail to the stochastic ellipsoid construction.")),
            Node("claim-1", "IsSeparated", "Is Separated",
                "IsSeparated ε N : N is a finite set of unit vectors, any two distinct ones at distance more than ε. Note that Mathlib has an unrelated Metric.IsSeparated; this one is D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.IsSeparated and shadows it inside this namespace only.", DescribeRole.Definition),
            Node("claim-2", "card_le_of_isSeparated", "card le of is Separated",
                "Packing count. An ε-separated set of unit vectors has at most (1 + 2/ε) ^ d elements, d = finrank ℝ E. The proof is the volume argument: the balls of radius ε/2 around the points are pairwise disjoint and contained in the ball of radius 1 + ε/2.", DescribeRole.Theorem),
            Node("claim-3", "exists_net", "exists net",
                "Existence of an ε-net of the unit sphere with an explicit cardinality bound. A maximal ε-separated set of unit vectors is an ε-net, and the packing count bounds its size. Existence of a maximal one is Nat.sSup_mem: the set of achievable cardinalities is a nonempty set of naturals bounded above by the packing count.", DescribeRole.Theorem),
            Node("claim-4", "opNorm_le_of_quadratic", "op Norm le of quadratic",
                "For a self-adjoint continuous linear map on a real inner product space, the operator norm is bounded by any bound on the quadratic form over the unit sphere. This is the classical polarization argument, proved here self-containedly. Mathlib carries the same fact in the form ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (‖T‖ = ⨆ x, |T.rayleighQuotient x| for a symmetric T), built on ContinuousLinearMap.opNorm_le_of_re_inner_le; deriving this statement from those is the shorter route.", DescribeRole.Theorem),
            Node("claim-5", "opNorm_le_of_net", "op Norm le of net",
                "The net bound (Vershynin, *High-Dimensional Probability*, Lemma 4.4.1, symmetric case). If the quadratic form of a self-adjoint T is bounded by M on an ε-net of the unit sphere, then (1 - 2ε) * ‖T‖ ≤ M.", DescribeRole.Theorem),
            Node("claim-6", "sum_sq_coeff_le", "sum sq coeff le",
                "For a unit vector x, the coefficients 2 x i x j of the quadratic form ⟪A x, x⟫ in the independent entries A i j have squares summing to at most 4. This is the variance-proxy computation of step (3) of the outline; the sum is over all pairs, which dominates the sum over i ≤ j, so the same bound serves after restriction.", DescribeRole.Theorem),
            Node("claim-7", "union_bound_arith", "union bound arith",
                "The numeric step of the union bound (step (5) of the outline): with an ε = 1/4 net of at most 9 ^ n unit vectors and the Chernoff exponent -(9/2) s² n obtained at u = 6 √c · s · √n, the union bound is dominated by exp (-s² n) for every s ≥ 1. Only Real.log 9 ≤ 3 is needed, so the constant has ample slack.", DescribeRole.Theorem),
            Node("claim-8", "hasSubgaussianMGF_mono", "has Subgaussian MGF mono",
                "Monotonicity of the sub-Gaussian parameter. Mathlib has HasSubgaussianMGF.const_mul, .neg, .add_of_indepFun and .sum_of_iIndepFun, but no monotonicity lemma at pin 6f1ef4e5; step (3) of the outline needs one to replace ∑ p, c p by a uniform bound.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
