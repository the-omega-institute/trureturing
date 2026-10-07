using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class PackingBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Packing Bounds"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate packing bounds to the stochastic ellipsoid construction.")),
            Node("claim-2", "r0_le_qrt", "r0 le qrt",
                "r₀ ≤ 8/q. log n/n ≤ 4/q³ ≤ 1/(9q²) because q ≥ 36, and the square root of the right-hand side is 1/(3q).", DescribeRole.Theorem),
            Node("claim-3", "eta_le_qrt", "eta le qrt",
                "η ≤ 1/q. η ≤ √2/n³ ≤ 2/q¹² ≤ 1/q.", DescribeRole.Theorem),
            Node("claim-4", "card_UT_pos", "card UT pos",
                "card (UT n) > 0.", DescribeRole.Theorem),
            Node("claim-5", "eta_pos", "eta pos",
                "η > 0: η² = 2·h·card·n and all three factors are positive.", DescribeRole.Theorem),
            Node("claim-6", "failTotal_nonneg", "fail Total nonneg",
                "failTotal is nonnegative.", DescribeRole.Theorem),
            Node("claim-7", "kappa_upper", "kappa upper",
                "1/mm² ≤ 1 + 8u, hence (1/2 + 2rr)/mm² ≤ 1/2 + 12u + 2rr.", DescribeRole.Theorem),
            Node("claim-8", "cq_of_Z", "cq of Z",
                "1/(2Z²) ≥ 1/2 − 4u − 3δ whenever 1 ≤ Z and Z² ≤ 1 + 8u + 6δ.", DescribeRole.Theorem),
            Node("claim-9", "cq_lower", "cq lower",
                "1/2 − 1/(2·MM²(1+δ)²) ≤ 4u + 3δ at MM ≤ 1 + 2u.", DescribeRole.Theorem),
            Node("claim-10", "driftCen_le", "drift Cen le",
                "driftCen ≤ κ((1+ε)·K·c²·dim + (1+1/ε)(c₃η)²) — TruncSumMean.integral_sum_sqTrunc_le on the truncated sum, the (1+1/ε) piece kept as it stands. This is the companion of TruncSumMean.driftCen_ge, in the direction hbudget needs.", DescribeRole.Theorem),
            Node("claim-11", "measureReal_compl_lt_tau_le_cut", "measure Real compl lt tau le cut",
                "On goodCut … K the stopping time exceeds K, so it exceeds every k ≤ K.", DescribeRole.Theorem),
            Node("claim-13", "hS_of_intWeight_cut", "h S of int Weight cut",
                "hS at the cut index. GoodPathBounds.hS_of_intWeight with the {k < τ} total collapsed against goodCut … K — the event whose count the tail side does supply.", DescribeRole.Theorem),
            Node("claim-14", "goodCut_fail_le", "good Cut fail le",
                "The goodCut failure is failTotal — goodPathCut's own union bound, extracted.", DescribeRole.Theorem),
            Node("claim-15", "numSteps_mul_step_eq", "num Steps mul step eq",
                "N·X = T·dim·(1 − 50/n) at the adopted parameters — TruncSumMean.driftCen_ge_adopted's own identity, extracted so a shorter horizon can use it.", DescribeRole.Theorem),
            Node("claim-16", "step_mul_dim_le_one", "step mul dim le one",
                "One step of the drift is at most 1: c²·dim = h·card ≤ n²/n⁹.", DescribeRole.Theorem),
            Node("claim-17", "log_div_le", "log div le",
                "log n/n ≤ 1/200 — sharper than AdoptedConstants95.log_ratio_le, and what the short-horizon hLb needs: log n ≤ 4q and n = q⁴ give log n/n ≤ 4/q³ ≤ 4/50 653.", DescribeRole.Theorem),
            Node("claim-19", "hLb_of_bounds_cut", "h Lb of bounds cut",
                "hLb with the drift horizon one step short of N — the two 4·log n cancel.", DescribeRole.Theorem),
            Node("claim-21", "thetaTight_combB_le", "theta Tight comb B le",
                "The combined threshold is n-free at B m = B₀/n².", DescribeRole.Theorem),
            Node("claim-22", "count_ratio_q", "count ratio q",
                "The count ratio, with the q³ kept. c₃'' = n²·q³, so a terminal weight θT ≤ Kc·n² gives a Markov ratio 2·Kc/q³ — the q³ is what makes log n · pcnt bounded.", DescribeRole.Theorem),
            Node("claim-23", "horizon_mul_card_le", "horizon mul card le",
                "T·dim ≤ 16·log n — the companion of TruncSumMean.horizon_mul_card_ge.", DescribeRole.Theorem),
            Node("claim-25", "failTotal_le_inv", "fail Total le inv",
                "failTotal n pcnt ≤ pcnt + 1/(1000·n).", DescribeRole.Theorem),
            Node("claim-26", "thetaTight_le_2800000", "theta Tight le 2800000",
                "The threshold at B₀ = 140, as a number: 3308·(32e² + 560) ≤ 2.64·10⁶.", DescribeRole.Theorem),
            Node("claim-28", "shortfall_le_twenty", "shortfall le twenty",
                "The shortfall total at t' = s' = 1, with both variance terms below 1.", DescribeRole.Theorem),
            Node("claim-29", "qrt_le_self", "qrt le self",
                "q ≤ q⁴ for q ≥ 37.", DescribeRole.Theorem),
            Node("claim-30", "delta_le_two_div", "delta le two div",
                "η/m ≤ 2/q from η ≤ 1/q and m ≥ 1/2.", DescribeRole.Theorem),
            Node("claim-31", "rr_le_twelve", "rr le twelve",
                "2·rr = 4η + 4c₃η ≤ 12/q.", DescribeRole.Theorem),
            Node("claim-32", "rm_ge", "rm ge",
                "(1+c₃)η ≤ rr·m at rr = 2(1+c₃)η and m ≥ 1/2.", DescribeRole.Theorem),
            Node("claim-33", "twenty_k_div_sq_le", "twenty k div sq le",
                "20000/q² ≤ 15 at q ≥ 37.", DescribeRole.Theorem),
            Node("claim-34", "gap_le", "gap le",
                "The gap, as bare arithmetic: κ(1+ε) − cq ≤ 183·(1/q) ≤ 200·(1/q).", DescribeRole.Theorem),
            Node("claim-35", "rhs_identity", "rhs identity",
                "The numerator identity. S = K·dim − Θ/h − dim·(K·pbad) and L = logDet A₀ − (driftCen + 1) − 1, so driftRHS_acc − L + 20 is the term list num_le_const bounds.", DescribeRole.Theorem),
            Node("claim-36", "kp_le_six", "kp le six",
                "κ(1+ε) ≤ 6 at κ ≤ 5, ε ≤ 1/5.", DescribeRole.Theorem),
            Node("claim-37", "twenty_k_div_cube_le", "twenty k div cube le",
                "20000/q³ ≤ 0.396 at q ≥ 37 (measured 0.394 8; the ceiling is chosen above it).", DescribeRole.Theorem),
            Node("claim-38", "vterm_le", "vterm le",
                "K·c²·(n/m²) ≤ 1: K·h ≤ T = 16 log n/n², n/m² ≤ 4n, and log n/n ≤ 1/200.", DescribeRole.Theorem),
            Node("claim-39", "wterm_le", "wterm le",
                "K·(η²/2)² ≤ 1: η²/2 = h·card·n, h ≤ n⁻⁹, card ≤ n², and K·h ≤ 16 log n/n².", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
