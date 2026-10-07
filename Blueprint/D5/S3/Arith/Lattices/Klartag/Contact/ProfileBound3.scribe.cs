using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound3"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound3 to the stochastic ellipsoid construction.")),
            Node("claim-1", "yOf_subst", "y Of subst",
                "yOf a₀ t (subst a₀ √t y) = y: the substitution is a right inverse of the paper's y(r).", DescribeRole.Theorem),
            Node("claim-2", "radiusOf", "radius Of",
                "The radius at which the profile takes the value Φ(y): the paper's substitution, un-scaled by α and shifted out by the cube radius δ.", DescribeRole.Definition),
            Node("claim-6", "profile_radiusOf", "profile radius Of",
                "The profile at the substituted radius is Φ. Both if-branches take their non-degenerate values — the radius is inside the window, and the shifted, scaled radius is positive — and yOf_subst collapses the rest.", DescribeRole.Theorem),
            Node("claim-8", "substituted_integrand_le", "substituted integrand le",
                "The substituted integrand, with the shift priced. Combining subst_integrand (the Jacobian and the r^{n−1} factor) with shift_constant (the cube shift, bounded by e^{1/2} under tiling_defect) and rpow_neg_le_of_one_le (normalising a₀ away). The right-hand side is exactly the integrand of I₁, I₂ and I₃, times e^{1/2}·√t/(2·αⁿ).", DescribeRole.Theorem),
            Node("claim-10", "integrand_eq_pieces", "integrand eq pieces",
                "PhiC = Φ on the positive reals, so the bound of integral_shell_le is the I₁/I₂/I₃ integrand with the constant e^{1/2}·√t/(2αⁿ) in front.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
