using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43CDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43C"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43c to the stochastic ellipsoid construction.")),
            Node("claim-1", "integral_exp_mul_Ioc", "integral exp mul Ioc",
                "∫₀^T e^{c·t} dt = (e^{c·T} − 1)/c.", DescribeRole.Theorem),
            Node("claim-2", "exp_n2T_eq", "exp n2T eq",
                "With T = 16·log n/n², the exponent is exactly 2·log n, so e^{n²T/8} = n².", DescribeRole.Theorem),
            Node("claim-3", "integral_exp_n2_eq", "integral exp n2 eq",
                "The t-integral of Lemma 4.3's bound, exactly. ∫₀ᵀ e^{n²t/8} dt = 8 − 8/n². No asymptotics: this is an identity at T = 16·log n/n². Verified numerically against quadrature to ten digits (/private/tmp/claude-501/b-l10-2/t_integral.py).", DescribeRole.Theorem),
            Node("claim-4", "T_nonneg", "T nonneg",
                "T = 16·log n/n² is non-negative for n ≥ 1.", DescribeRole.Theorem),
            Node("claim-5", "antitone_integral", "antitone integral",
                "An integral of antitone functions is antitone.", DescribeRole.Theorem),
            Node("claim-6", "integral_nonneg_of_nonneg", "integral nonneg of nonneg",
                "The t-integrated profile is non-negative.", DescribeRole.Theorem),
            Node("claim-7", "lintegral_radial_t_swap", "lintegral radial t swap",
                "Tonelli for the radial/t pair. The ℝ≥0∞ swap; only measurability is needed.", DescribeRole.Theorem),
            Node("claim-8", "lintegral_radial_t_le", "lintegral radial t le",
                "The t-integrated radial bound in ℝ≥0∞. Feed the fixed-t Lemma 4.3 bound ∫ y ≤ C₁·e^{n²t/8} and get ∫ y ∫ t ≤ C₁·(8 − 8/n²) — the exact constant of §1.", DescribeRole.Theorem),
            Node("claim-10", "radial_bound_of_lintegral", "radial bound of lintegral",
                "From an ℝ≥0∞ bound to RadialWeightData.radial_bound. The Bochner statement the structure wants, recovered from the ℝ≥0∞ one under integrability.", DescribeRole.Theorem),
            Node("claim-11", "lintegral_t_ofReal", "lintegral t of Real",
                "Pulling y^{n−1} and the t-integral through ENNReal.ofReal.", DescribeRole.Theorem),
            Node("claim-12", "eight_sub_nonneg", "eight sub nonneg",
                "8 − 8/n² ≥ 0 for n ≥ 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
