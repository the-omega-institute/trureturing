using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound5"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound5 to the stochastic ellipsoid construction.")),
            Node("claim-1", "image_radiusOf_Ioc", "image radius Of Ioc",
                "radiusOf '' (0, Y] = (radiusOf 0, radiusOf Y]. ⊇ is the intermediate value theorem (shell_subset_image); ⊆ is strict monotonicity. Getting the *equality* rather than a containment is what keeps the assembly short: no measurability of an abstract image is needed.", DescribeRole.Theorem),
            Node("claim-2", "shell_integral_le", "shell integral le",
                "The shell integral becomes the I₁/I₂/I₃ integral. integral_shell_eq through the image identity, then integral_shell_le, then integrand_eq_pieces pulls the constant out.", DescribeRole.Theorem),
            Node("claim-3", "hgbound_final", "hgbound final",
                "hgbound for the concrete profile, with the constant written out: the inner ball, the shift-and-Jacobian factor, and the three pieces.", DescribeRole.Theorem),
            Node("claim-4", "pieces_sum_le", "pieces sum le",
                "The three pieces summed, with the prefactor.", DescribeRole.Theorem),
            Node("claim-5", "shell_le_pieces", "shell le pieces",
                "The shell integral, bounded by the three pieces' constant. Composing shell_integral_le with pieces_sum_le: the √t/2 of the former is 1/n times the n√t/2 the pieces carry, which is where the 1/n in C₁ comes from.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
