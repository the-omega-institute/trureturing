using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound4"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound4 to the stochastic ellipsoid construction.")),
            Node("claim-1", "integral_pow_Ioc", "integral pow Ioc",
                "∫₀^ρ r^{n−1} dr = ρⁿ/n.", DescribeRole.Theorem),
            Node("claim-2", "inner_ball_le", "inner ball le",
                "The inner-ball piece. On (0, ρ] the profile is at most 1/2 (it is exactly 1/2 below the shell), so the piece contributes ρⁿ/(2n).", DescribeRole.Theorem),
            Node("claim-4", "shell_subset_image", "shell subset image",
                "The shell is covered by the window's image. intermediate_value_Ioc, with radiusOf continuous on [0, Y].", DescribeRole.Theorem),
            Node("claim-5", "window_split", "window split",
                "∫₀^W = ∫₀^ρ + ∫_ρ^W, the inner ball plus the shell.", DescribeRole.Theorem),
            Node("claim-6", "window_le", "window le",
                "The window integral, bounded by the inner ball plus the shell. The shape the final assembly consumes: the fourth piece explicit, the shell handed to integral_shell_le.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
