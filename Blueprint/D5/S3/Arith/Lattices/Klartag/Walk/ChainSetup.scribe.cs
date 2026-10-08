using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainSetupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Setup"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain setup to the stochastic ellipsoid construction.")),
            Node("claim-1", "gaussPath", "gauss Path",
                "The path space: one standard Gaussian per step, for infinitely many steps.", DescribeRole.Definition),
            Node("claim-2", "coord", "coord",
                "The k-th driving increment.", DescribeRole.Definition),
            Node("claim-4", "map_coord", "map coord",
                "The law of each coordinate is the standard Gaussian.", DescribeRole.Theorem),
            Node("claim-5", "iIndepFun_coord", "i Indep Fun coord",
                "The coordinates are independent.", DescribeRole.Theorem),
            Node("claim-6", "restr", "restr",
                "The first k increments.", DescribeRole.Definition),
            Node("claim-8", "natFil", "nat Fil",
                "The natural filtration of the driving sequence.", DescribeRole.Definition),
            Node("claim-11", "filtration", "filtration",
                "The filtration, bundled.", DescribeRole.Definition),
            Node("claim-12", "measurable_coord_natFil", "measurable coord nat Fil",
                "ξ k is ℱ (k+1)-measurable — the sequence is adapted.", DescribeRole.Theorem),
            Node("claim-13", "indepFun_coord_restr", "indep Fun coord restr",
                "ξ k is independent of the first k increments.", DescribeRole.Theorem),
            Node("claim-16", "memLp_coord_apply", "mem Lp coord apply",
                "All moments of every coordinate are finite, from memLp_id_gaussianReal.", DescribeRole.Theorem),
            Node("claim-18", "integrable_norm_sq_coord", "integrable norm sq coord",
                "‖ξ_k‖² is integrable — the second moment that dominates hintquad, since ‖π x‖ ≤ ‖x‖.", DescribeRole.Theorem),
            Node("claim-19", "step", "step",
                "The chain's increment: the standard coordinate scaled by c = √h.", DescribeRole.Definition),
            Node("claim-21", "map_step", "map step",
                "ξ_k ~ N(0, c²·Id) — the currency StateInvariant4's half-laws take.", DescribeRole.Theorem),
            Node("claim-23", "step_coord_law", "step coord law",
                "hlaw of driftInputs_step_chain, at v = c².", DescribeRole.Theorem),
            Node("claim-24", "step_coord_indep", "step coord indep",
                "hindep of driftInputs_step_chain.", DescribeRole.Theorem),
            Node("claim-25", "indep_step_natFil", "indep step nat Fil",
                "hind of driftInputs_step_chain: each increment is independent of its own past.", DescribeRole.Theorem),
            Node("claim-27", "integrable_step_apply", "integrable step apply",
                "hintxi of driftInputs_step_chain.", DescribeRole.Theorem),
            Node("claim-28", "integrable_step_mul", "integrable step mul",
                "hintprod of driftInputs_step_chain.", DescribeRole.Theorem),
            Node("claim-30", "integrable_bddCoeff_mul", "integrable bdd Coeff mul",
                "hintK: a coefficient bounded by C times a product of two coordinates is integrable as soon as the coefficient is a.e. strongly measurable. For driftInputs_step_chain the coefficient is (π_k e_p) q, bounded by ‖π_k e_p‖ ≤ ‖e_p‖ = 1.", DescribeRole.Theorem),
            Node("claim-31", "norm_coord_le", "norm coord le",
                "A coordinate is bounded by the norm.", DescribeRole.Theorem),
            Node("claim-32", "abs_starProjection_single_le_one", "abs star Projection single le one",
                "The bound integrable_bddCoeff_mul is applied at: an orthogonal projection's matrix entries are at most 1 in absolute value.", DescribeRole.Theorem),
            Node("claim-36", "chainDir", "chain Dir",
                "The chain direction, in the first summand.", DescribeRole.Definition),
            Node("claim-37", "freshDir", "fresh Dir",
                "The fresh direction: the second summand's unit vector.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
