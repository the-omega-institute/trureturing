using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound to the stochastic ellipsoid construction.")),
            Node("claim-1", "lintegral_profile_eq_ofReal", "lintegral profile eq of Real",
                "The ℝ≥0∞ integral of the profile is the ofReal of its Bochner integral.", DescribeRole.Theorem),
            Node("claim-2", "hgbound_of_bochner", "hgbound of bochner",
                "hgbound from a real bound. Everything ℝ≥0∞ is discharged here, so the three-piece split may be carried out entirely over ℝ.", DescribeRole.Theorem),
            Node("claim-3", "hgbound_of_window", "hgbound of window",
                "The same, restricted to the window — the form the split consumes.", DescribeRole.Theorem),
            Node("claim-4", "pow_add_le_exp_mul", "pow add le exp mul",
                "(u + c)^m ≤ e^{m·c/u₀}·u^m for u ≥ u₀ > 0 and c ≥ 0.", DescribeRole.Theorem),
            Node("claim-5", "setIntegral_Ioc_split", "set Integral Ioc split",
                "Two-piece additivity on Ioc.", DescribeRole.Theorem),
            Node("claim-7", "I2_le", "I2 le",
                "I₂ with its prefactor, bounded by an absolute constant times e^{n²t/8}. This is Klartag's eq. (59) together with eq. (56)'s prefactor, complete. The constant is e^J·(2/√(2π) + 2), where J bounds the junk term of Lemma43.integrand_le on (1, L].", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
