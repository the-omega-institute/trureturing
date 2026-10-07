using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound8Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound8"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound8 to the stochastic ellipsoid construction.")),
            Node("claim-1", "junk_le_of_endpoint", "junk le of endpoint",
                "The junk hypothesis, reduced to its endpoint. y ↦ y·s + c·(y·s)² is monotone on y ≥ 0 for s, c ≥ 0, so hJ's ∀ y ∈ Ioc A B follows from the single value at y = B.", DescribeRole.Theorem),
            Node("claim-4", "integrableOn_shell_lhs", "integrable On shell lhs",
                "Shape 4's certificate. The change-of-variables integrand is bounded on the window: the Jacobian by window_gap + substDeriv_le, the radius by radiusOf_le_end, the profile by 1/2.", DescribeRole.Theorem),
            Node("claim-5", "hgbound_chained", "hgbound chained",
                "hgbound for the concrete profile, chained. shell_integral_le → shell_le_pieces → hgbound_final, with the constant ρⁿ/(2n) + (e^{1/2}/(n·αⁿ))·(K₁ + K₂ + K₃)·e^{n²t/8}, ρ = radiusOf 0. Every hypothesis is now supplied by a lemma of ProfileBound6/ProfileBound7.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
