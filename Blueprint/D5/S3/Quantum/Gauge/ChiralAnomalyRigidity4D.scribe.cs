using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class ChiralAnomalyRigidity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.";
    private static readonly AssessedProvenance MajoranaSource =
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/LieTheory/babumohapatra1989majorana"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local anomaly cancellation, charge quantization, and Weyl traces for one generation.",
        H("Chiral anomalies and charge rigidity in four dimensions"),
        Blocks(
            Paragraph(Text(
                "Write n = N_c for the number of colors and y = (y_Q, y_u, y_d, y_L, y_e, y_n) " +
                "for one generation in all-left-handed notation. The u, d, e, and n singlets are " +
                "charge conjugates of the right-handed particles. The four local equations are " +
                "2y_Q + y_u + y_d = 0, ny_Q + y_L = 0, " +
                "2ny_Q + ny_u + ny_d + 2y_L + y_e + y_n = 0, and " +
                "2ny_Q³ + ny_u³ + ny_d³ + 2y_L³ + y_e³ + y_n³ = 0. " +
                "The algebraic classifications use a field of characteristic zero.")),
            Node("cubic-factorization", "cubic_anomaly_factorization", "Factorization of the cubic",
                "Over any field, impose the three linear equations and put t = y_u + y_Q and " +
                "w = y_e − ny_Q. The cubic polynomial is exactly 6ny_Q(w − t)(w + t)."),
            Node("anomaly-free-planes", "anomaly_free_planes_iff", "The three anomaly-free planes",
                "For n ≥ 1, all four equations hold exactly on the union of the planes " +
                "Π₊(a,t) = (a, t − a, −t − a, −na, na − t, na + t), " +
                "Π₋(a,t) = (a, t − a, −t − a, −na, na + t, na − t), and " +
                "Π₀(b,c) = (0, b, −b, 0, c, −c), with parameters in the field."),
            Node("one-color-counterexample", "nc_one_counterexample", "The color equation at one color",
                "At n = 1, (1, 1, −1, −1, 0, 0) satisfies the weak, mixed gravitational, " +
                "and cubic equations and lies outside the union of the three planes."),
            Node("neutrino-free-lines", "anomaly_free_lines_without_nuR_iff", "The three lines with neutral singlet",
                "For n ≥ 1, the four anomalies vanish and y_n = 0 exactly on the lines " +
                "a(1, −(n + 1), n − 1, −n, 2n, 0), " +
                "a(1, n − 1, −(n + 1), −n, 2n, 0), and (0, b, −b, 0, 0, 0)."),
            Node("dirac-yukawa-on-plane", "dirac_yukawa_pi_plus_iff", "Dirac Yukawa equations on Π₊",
                "Over any field, with Higgs hypercharge h, the four equations " +
                "y_Q + h + y_u = 0, y_Q − h + y_d = 0, y_L − h + y_e = 0, " +
                "and y_L + h + y_n = 0 hold on Π₊(a,t) exactly when t = −h."),
            Node("dirac-bl-family", "dirac_yukawa_bl_family_iff", "The Dirac B−L family",
                "For n ≥ 1, the anomalies and the four Dirac Yukawa equations vanish exactly " +
                "when y = Y₀ + ε(1/n, −1/n, −1/n, −1, 1, 1) for a unique field element ε, " +
                "where Y₀ = Π₊(h/n, −h). The vector multiplying ε is B−L in the all-left-handed " +
                "convention.", MajoranaSource),
            Node("majorana-quantization", "majorana_restores_charge_quantization", "Majorana quantization",
                "For n ≥ 1, the anomalies, Dirac Yukawa equations, and Majorana equation " +
                "2y_n = 0 hold exactly when y = Π₊(h/n, −h). The Majorana equation sets ε = 0.",
                MajoranaSource),
            Node("dirac-electric-charges", "dirac_family_electric_charges", "The electric charges along the Dirac family",
                "At h = 1/2 and n ≥ 1, the particle charges u, d, ν, e are " +
                "((n + 1)/(2n) + ε/n, −(n − 1)/(2n) + ε/n, −ε, −1 − ε). " +
                "The generation sum n(Q_u + Q_d) + Q_ν + Q_e vanishes for every ε."),
            Node("quantized-electric-charges", "quantized_electric_charges", "The quantized electric charges",
                "At h = 1/2 and n ≥ 1, Y₀ has particle charges " +
                "((n + 1)/(2n), −(n − 1)/(2n), 0, −1) and generation sum zero."),
            Node("fixed-quark-rigidity", "quark_charges_uniquely_select_nc_three", "Three colors from fixed quark weights",
                "For n ≥ 1, set (y_Q, y_u, y_d) = (1/6, −2/3, 1/3) and y_n = 0. " +
                "The anomalies vanish exactly when n = 3, y_L = −1/2, and y_e = 1. " +
                "The linear equations give y_L = −n/6 and y_e = n/3, and the cubic becomes " +
                "n(n − 3)(n + 3)/36. At three colors the weights are those of the finite " +
                "spectral triple."),
            Node("quantized-weyl-traces", "weyl_traces_quantized", "Weyl traces on the quantized family",
                "For n ≥ 1 and h = 1/2, the one-generation Weyl traces at Y₀ are " +
                "Tr(T_c²) = 2, Tr(T₃²) = (n + 1)/2, Tr(T₃Y) = 0, " +
                "Tr(Y²) = (n + 1)(n + 2)/(2n), and Tr(Q²) = (n + 1)²/n. " +
                "Use fundamental color normalization 1/2, continued algebraically to n = 1. " +
                "The ratio Tr(T₃²)/(Tr(T₃²) + Tr(Y²)) gives the curve s_anom(n) = n/(2(n + 1))."),
            Node("equal-color-weak-traces", "weyl_arc_trace_nc_three_and_weinberg_angle",
                "Three colors from equal Weyl traces",
                "The color and weak generator traces agree exactly at n = 3, where " +
                "k_Y = Tr(Y²)/Tr(T₃²) = 5/3 on the quantized family and s_anom(3) = 3/8."),
            Node("fixed-charge-weak-mixing", "fixed_charge_weak_mixing", "The fixed-charge mixing curve",
                "With the rational hypercharge table of the finite spectral triple and n " +
                "quark colors, the ratio Tr(T₃²)/(Tr(T₃²) + Tr(Y²)) is " +
                "s_fixed(n) = 9(n + 1)/(4(9 + 5n))."),
            Node("weinberg-angle-difference", "weinberg_angle_difference", "Difference of the mixing curves",
                "For natural n, s_anom(n) − s_fixed(n) = (n − 3)(n + 3)/(4(n + 1)(9 + 5n))."),
            Node("weinberg-angle-intersection", "weinberg_angle_intersection_iff", "The mixing-curve intersection",
                "For natural n, the curves agree exactly at n = 3. Their common value is 3/8."))));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
