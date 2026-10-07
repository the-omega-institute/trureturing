using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43UniformDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Uniform"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform to the stochastic ellipsoid construction.")),
            Node("claim-1", "PhiC_yOf_mono", "Phi C y Of mono",
                "t ↦ PhiC (yOf a₀ t u) is monotone: yOf is c/√t, which decreases in t when c ≥ 0 (and PhiC is antitone), while for c < 0 both values are negative and PhiC is 1/2 at both.", DescribeRole.Theorem),
            Node("claim-2", "profile_mono_time", "profile mono time",
                "The profile is monotone in t. This is what the small-t branch runs on.", DescribeRole.Theorem),
            Node("claim-3", "radiusOf_zero_eq", "radius Of zero eq",
                "radiusOf at y = 0 is t-free: this is why Lemma 4.3's inner-ball term is a constant.", DescribeRole.Theorem),
            Node("claim-4", "radiusOf_yOf", "radius Of y Of",
                "radiusOf inverts yOf. This is the reparameterisation.", DescribeRole.Theorem),
            Node("claim-8", "rhoC", "rho C",
                "radiusOf a₀ α (√n/2) t 0, written t-free.", DescribeRole.Definition),
            Node("claim-9", "Kc", "Kc",
                "pieces_at_params' constant: K = e⁶ + e³(2/√(2π) + 2) + 2e³.", DescribeRole.Definition),
            Node("claim-13", "integrable_radial_euclidean", "integrable radial euclidean",
                "Params.integrable, discharged.", DescribeRole.Theorem),
            Node("claim-14", "a0C", "a0C",
                "Klartag's a₀ = (1 − 1/n)⁻², p. 21 eq. (61).", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
