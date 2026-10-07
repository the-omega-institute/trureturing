using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound6Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound6"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound6 to the stochastic ellipsoid construction.")),
            Node("claim-3", "rpow_factor_le", "rpow factor le",
                "The uniform bound on the window. y·√t ≤ 1/2 gives (1 − y√t)^{−c} ≤ (1/2)^{−c}, with no n and no t in it.", DescribeRole.Theorem),
            Node("claim-4", "integrableOn_pieces", "integrable On pieces",
                "I₁/I₂/I₃'s hint1, and pieces_sum_le's i1, i2, i3. Bounded by (1/2)·(1/2)^{−(n+2)/2} on the window, measurable, finite measure.", DescribeRole.Theorem),
            Node("claim-5", "integrableOn_rhs", "integrable On rhs",
                "I₂'s and I₃'s hint2. On Ioc A B with A ≥ 1 the factor 1/y is at most 1, so the whole integrand is bounded by its constant times 1.", DescribeRole.Theorem),
            Node("claim-6", "integrableOn_profile_sub", "integrable On profile sub",
                "hgbound_final's h1 and h2. integrableOn_profile_radial restricted.", DescribeRole.Theorem),
            Node("claim-8", "substDeriv_le", "subst Deriv le",
                "The Jacobian is bounded where a₀ − √t·y is bounded away from zero.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
