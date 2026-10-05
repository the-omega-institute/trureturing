using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailSideSetupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Side Setup"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail side setup to the stochastic ellipsoid construction.")),
            Node("claim-1", "prod_map_middle_four", "prod map middle four",
                "The middle-four interchange for product measures. Not in Mathlib; proved on rectangles by Fubini twice.", DescribeRole.Theorem),
            Node("claim-2", "indepFun_prodMk_prodMk", "indep Fun prod Mk prod Mk",
                "Two independent pairs of blocks, one pair per factor.", DescribeRole.Theorem),
            Node("claim-3", "indepFun_fst_prod", "indep Fun fst prod",
                "A block on the first factor against a block on the first factor together with all of the second.", DescribeRole.Theorem),
            Node("claim-4", "stdGaussian_real", "std Gaussian real",
                "stdGaussian ℝ is N(0,1) — the bridge between the value type's second summand and the external factor's law.", DescribeRole.Theorem),
            Node("claim-5", "PadSpace", "Pad Space",
                "The space of the external-padding route: the chain's path space times the k fresh Gaussians TailTransport.hit_tail_yOf asks for.", DescribeRole.Definition),
            Node("claim-7", "Zed", "Zed",
                "The past at step i: the first i chain coordinates and the first i fresh ones.", DescribeRole.Definition),
            Node("claim-9", "Xi", "Xi",
                "The combined increment below the horizon, rescaled so that it is a *standard* Gaussian on the two-factor value type: the chain coordinate and the fresh coordinate divided by r.", DescribeRole.Definition),
            Node("claim-11", "map_Xi", "map Xi",
                "Its law is standard: map_pair_prod, with the fresh coordinate rescaled.", DescribeRole.Theorem),
            Node("claim-12", "indepFun_Zed_Xi", "indep Fun Zed Xi",
                "The past is independent of the increment — the four blocks straddle the two factors, which is what §1 is for.", DescribeRole.Theorem),
            Node("claim-13", "trunc", "trunc",
                "The past, truncated further — used to say that the earlier increments are functions of the past at step i.", DescribeRole.Definition),
            Node("claim-15", "Xfam", "Xfam",
                "The increment family. Below the horizon it is the padded increment — the chain coordinate and the fresh one read in a past-measurable unit direction. At and above the horizon there is no fresh coordinate, so the increment is an unused chain coordinate read in a fixed unit direction; that completion is exactly what PaddingMap.map_pi_of_stepIndep's ∀ i hypotheses need.", DescribeRole.Definition),
            Node("claim-17", "map_Xfam", "map Xfam",
                "Every increment is N(0, r²) — below the horizon by the frozen-direction argument on the two-factor value type, above it by map_scaled_inner at the unused chain coordinate.", DescribeRole.Theorem),
            Node("claim-18", "Gfam", "Gfam",
                "The earlier increments, as a function of the past at step i.", DescribeRole.Definition),
            Node("claim-21", "indepFun_Xfam", "indep Fun Xfam",
                "Each increment is independent of all the earlier ones.", DescribeRole.Theorem),
            Node("claim-22", "hincl_external", "hincl external",
                "hincl at every horizon on the external-padding route.", DescribeRole.Theorem),
            Node("claim-23", "inner_toLp_padUnit", "inner to Lp pad Unit",
                "The completed unit direction, written out at the two-factor carrier.", DescribeRole.Theorem),
            Node("claim-25", "hincl_of_increments", "hincl of increments",
                "hincl for an adapted increment family — TailTransport.hit_tail_yOf's law, with the chain entering only through hM: its increment at step i is r⟪ω i, w_i(past)⟫, and the padding amplitude is the completing √(1 − ‖w_i‖²).", DescribeRole.Theorem),
            Node("claim-26", "tail_of_increments", "tail of increments",
                "The transported per-step tail for an adapted increment family, on the chain's own path space, with no probabilistic hypothesis left.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
