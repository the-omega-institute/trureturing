using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class Section5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/Section5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Section5"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate section5 to the stochastic ellipsoid construction.")),
            Node("claim-1", "kappa", "kappa",
                "κ_n = Vol_n(Bⁿ), as a real number.", DescribeRole.Definition),
            Node("claim-4", "two_lt_exp_three_quarters", "two lt exp three quarters",
                "2 < exp (3/4), via exp (3/4) = exp (1/8) ^ 6 ≥ (9/8) ^ 6 = 531441/262144.", DescribeRole.Theorem),
            Node("claim-5", "two_mul_pow_lt_one", "two mul pow lt one",
                "The Use-1 arithmetic core: x ≤ 1 - 1/n + δ with n·δ ≤ 1/4 forces 2·xⁿ < 1. This replaces Klartag's (1-1/n)ⁿ ≤ 1/e and is *stronger*: e^{-3/4} < 1/2, so the union bound gets 1/2 + 1/2 rather than 1/e + 1/2, with strictness to spare.", DescribeRole.Theorem),
            Node("claim-7", "two_mul_card_lt", "two mul card lt",
                "The integer-point count of a ball, in the form the union bound consumes.", DescribeRole.Theorem),
            Node("claim-8", "use_one_arith", "use one arith",
                "The Use-1 volume condition, discharged. Under Klartag's normalisation αⁿ·m = κ_n (so that α·Λ(g) has covolume κ_n), a scaled radius α·(R + √n/2) ≤ 1 - 1/n + δ with n·δ ≤ 1/4 gives the hypothesis of two_mul_card_lt.", DescribeRole.Theorem),
            Node("claim-9", "two_mul_card_bad_one_lt", "two mul card bad one lt",
                "Use 1 (eq. 64), discrete counterpart. Fewer than half of the pⁿ-1 lines meet the small ball at all.", DescribeRole.Theorem),
            Node("claim-10", "sum_weight_onLine", "sum weight on Line",
                "Weighted first-moment lemma. The same swap of two finite sums as ConstructionA.sum_card_filter_onLine, with weights — this is what eq. (65)'s K̃_t (a sum of Φ-values, not a bare count) actually needs.", DescribeRole.Theorem),
            Node("claim-12", "card_bad_two_weighted_le", "card bad two weighted le",
                "Weighted Markov (eq. 66).", DescribeRole.Theorem),
            Node("claim-13", "two_mul_card_bad_two_lt", "two mul card bad two lt",
                "Use 2 (eq. 66), discrete counterpart. Fewer than half of the lines carry a weighted contact sum of θ or more.", DescribeRole.Theorem),
            Node("claim-14", "weight_bound_of_lintegral", "weight bound of lintegral",
                "From an integral bound to ChainData.weight_bound. This is the connector between Lemma 4.3 (∫ Φ ≤ C₁κ_n e^{n²t/8}, evaluated by polar coordinates — the Mathlib entry point is MeasureTheory.Measure.integral_fun_norm_addHaar, Constructions/HaarToSphere.lean:296) and the finite Markov step. The domination hypothesis hdom is where radial monotonicity of Φ is used: on the cube at y, Φ at y is below Φ at the *inner* radius.", DescribeRole.Theorem),
            Node("claim-15", "exists_good_line", "exists good line",
                "Proposition 5.1 (Construction A form), weighted. 1/2 + 1/2 < 1: Use 1 kills fewer than half the lines, Use 2 kills fewer than half, so a line survives both.", DescribeRole.Theorem),
            Node("claim-17", "exists_good_line_of_chainData", "exists good line of chain Data",
                "§5's output. A single Construction-A line g that is simultaneously lattice-free in the small ball (Klartag's eq. 64) and light in contacts (his eq. 66).", DescribeRole.Theorem),
            Node("claim-18", "redMod_ne_zero_of_norm_lt", "red Mod ne zero of norm lt",
                "p-indivisibility from a norm bound, pointwise. This is the pointwise form of ConstructionA.redMod_ne_zero_of_abs_lt, and it is what discharges ChainData.ball_indivisible from R < p.", DescribeRole.Theorem),
            Node("claim-19", "exists_prime_alpha_le", "exists prime alpha le",
                "For every n ≥ 2 and every ε > 0 a prime p makes the Klartag scale α ≤ ε. α = (κ_n / p^{n-1})^{1/n} → 0 as p → ∞, and p appears nowhere in the conclusion.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
