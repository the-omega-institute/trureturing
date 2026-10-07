using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GaussianMaximalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("Gaussian Maximal"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal to the stochastic ellipsoid construction.")),
            Node("claim-1", "maxNorm", "max Norm",
                "The running maximum of the increments' norms.", DescribeRole.Definition),
            Node("claim-3", "le_maxNorm", "le max Norm",
                "Every increment before N is below the maximum — the pointwise fact the stopping-time corollary runs on.", DescribeRole.Theorem),
            Node("claim-4", "norm_at_index_le_maxNorm", "norm at index le max Norm",
                "The stopping-time corollary. For any index function τ with τ ω < N, the increment read at τ is below the maximum, pointwise — so its expectation is too.", DescribeRole.Theorem),
            Node("claim-5", "exists_le_of_lt_maxNorm", "exists le of lt max Norm",
                "If the running maximum exceeds a non-negative level, some increment does.", DescribeRole.Theorem),
            Node("claim-7", "maxNorm_tail", "max Norm tail",
                "The maximum's tail, normalised. With σ² = v·d the union bound over the N steps and the d coordinates gives a *standard* Gaussian tail in t.", DescribeRole.Theorem),
            Node("claim-9", "lintegral_maxNorm_le", "lintegral max Norm le",
                "The maximal inequality, in lintegral form. No integrability hypothesis.", DescribeRole.Theorem),
            Node("claim-10", "expectation_max_norm_le", "expectation max norm le",
                "The maximal inequality, in Bochner form.", DescribeRole.Theorem),
            Node("claim-11", "expectation_max_norm_le_log", "expectation max norm le log",
                "The maximal inequality with the level chosen. At a = √(2·log K) with K = 2dN, the tail term is exactly σ/a ≤ σ, so E[max_{k<N} ‖ξ_k‖] ≤ σ·(√(2·log(2dN)) + 1), σ = √(v·d). The only size condition is K ≥ e, which holds as soon as there are two steps in dimension two.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
