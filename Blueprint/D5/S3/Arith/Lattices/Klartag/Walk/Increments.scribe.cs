using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class IncrementsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/Increments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Increments"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate increments to the stochastic ellipsoid construction.")),
            Node("claim-1", "map_stdGaussian_isometry", "map std Gaussian isometry",
                "Rotational invariance. The standard Gaussian on a finite-dimensional real inner product space is invariant under every linear isometry equivalence. This is the one-line replacement for the use of Lévy's characterisation in Klartag's Lemma 3.1.", DescribeRole.Theorem),
            Node("claim-2", "charFun_map_of_inner", "char Fun map of inner",
                "The characteristic function of a pushforward, when the map has an explicit \"adjoint\". Stated without ContinuousLinearMap.adjoint so that no CompleteSpace hypothesis is needed and the formula can be used for maps into a different space.", DescribeRole.Theorem),
            Node("claim-3", "UT", "UT",
                "The upper triangle, including the diagonal: the index set of the coordinates of a symmetric matrix.", DescribeRole.Definition),
            Node("claim-4", "up", "up",
                "The sorted pair (min i j, max i j).", DescribeRole.Definition),
            Node("claim-8", "cc", "cc",
                "The coordinate weight: 1 on the diagonal, 1/√2 off it. These are the coefficients that make symMat a Frobenius isometry.", DescribeRole.Definition),
            Node("claim-11", "symMat", "sym Mat",
                "The symmetric matrix with the given Frobenius coordinates.", DescribeRole.Definition),
            Node("claim-16", "fiber_up", "fiber up",
                "The fibre of the sorting map over p is the (possibly degenerate) pair {(a,b), (b,a)}.", DescribeRole.Theorem),
            Node("claim-17", "sum_symMat_mul", "sum sym Mat mul",
                "symMat is a Frobenius isometry. This is what justifies modelling R^{n×n}_sym by EuclideanSpace ℝ (UT n): the Euclidean inner product of the coordinates is the Frobenius inner product ∑_{i,j} A_ij B_ij of the matrices.", DescribeRole.Theorem),
            Node("claim-19", "mkMat", "mk Mat",
                "The symmetric matrix with prescribed upper-triangular entries.", DescribeRole.Definition),
            Node("claim-20", "mkCLM", "mk CLM",
                "mkMat followed by Matrix.toEuclideanCLM, bundled as a linear map so that its continuity is LinearMap.continuous_of_finiteDimensional.", DescribeRole.Definition),
            Node("claim-22", "coordVec", "coord Vec",
                "The Frobenius coordinates of the scaled symmetric Gaussian matrix.", DescribeRole.Definition),
            Node("claim-25", "Aux", "Aux",
                "The auxiliary probability space carrying a matrix with i.i.d. entries: a product indexed by the upper triangle and then by the two independent slots B a b and B b a.", DescribeRole.Definition),
            Node("claim-27", "auxB", "aux B",
                "The matrix with i.i.d. entries.", DescribeRole.Definition),
            Node("claim-28", "eIdx", "e Idx",
                "The index map (i,j) ↦ (sorted pair, slot); it is injective, which is why the entries of auxB are independent over the full product.", DescribeRole.Definition),
            Node("claim-35", "auxB_indep", "aux B indep",
                "The first hypothesis D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail consumes: the entries of auxB are independent over the full product Fin n × Fin n.", DescribeRole.Theorem),
            Node("claim-36", "auxB_law", "aux B law",
                "The second hypothesis D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail consumes: every entry of auxB is N(0, v).", DescribeRole.Theorem),
            Node("claim-37", "phi", "phi",
                "The block map producing the symmetrised entry from the two independent slots.", DescribeRole.Definition),
            Node("claim-43", "vOf", "v Of",
                "v = r²/4: the entry variance of the i.i.d. matrix that matches the scaling r of the symmetric Gaussian.", DescribeRole.Definition),
            Node("claim-44", "varOf", "var Of",
                "The variance of the symmetrised entry at p: r² on the diagonal, r²/2 off it — Klartag's E Γ_ij ^ 2 = (1 + δ_ij)/n after the scaling r = √(2/n).", DescribeRole.Definition),
            Node("claim-51", "map_coordVec_eq_map_auxV", "map coord Vec eq map aux V",
                "The law of the symmetric Gaussian matrix is the law of B + Bᵀ with i.i.d. B. This is Lemma 3.1's output in discrete form: it is what lets D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail, whose matrix is B + Bᵀ with independent entries over the full product, be applied to the chain's increment, whose entries above and below the diagonal are *equal* and therefore not independent.", DescribeRole.Theorem),
            Node("claim-55", "increment_opNorm_tail", "increment op Norm tail",
                "Klartag, Corollary 3.2, for the discrete chain's increment. If ξ is a standard Gaussian on the model EuclideanSpace ℝ (UT n) of R^{n×n}_sym, then the symmetric matrix r · symMat ξ — which is the increment of the Dyson walk after time r², E (W_t)_ij² = t (1 + δ_ij)/2 — satisfies, for every s ≥ 1, P(‖r · symMat ξ‖_op ≥ 6 r s √n) ≤ 4 exp (-s² n). The proof runs D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail on the auxiliary i.i.d. space and transports the conclusion along map_coordVec_eq_map_auxV.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
