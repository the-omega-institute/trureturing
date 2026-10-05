using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Profile.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile to the stochastic ellipsoid construction.")),
            Node("claim-1", "PhiC", "Phi C",
                "Φ with the paper's Φ(0) = 1/2 restored. Phi 0 = min (1/2) 0 = 0 in Lean.", DescribeRole.Definition),
            Node("claim-6", "Phi_antitoneOn", "Phi antitone On",
                "Φ is antitone on (0,∞): both e^{−y²/2} and 1/y decrease.", DescribeRole.Theorem),
            Node("claim-9", "yOf", "y Of",
                "y(r) = t^{−1/2}·(a₀ − r^{−2}), the paper's substitution variable (p. 20).", DescribeRole.Definition),
            Node("claim-10", "yOf_monotoneOn", "y Of monotone On",
                "y(·) is monotone on (0,∞) — and only there; it is even in r.", DescribeRole.Theorem),
            Node("claim-12", "profile", "profile",
                "Klartag's Lemma 4.3 integrand, concretely. profile a₀ α W n t r: * 0 beyond the window W — the shell R_t is bounded (eq. 55), and this is what makes the profile integrable; * 1/2 when the inward-shifted, scaled radius α·(r − √n/2) is non-positive — below the shell the weight is Φ(0) = 1/2, and this branch is what keeps the profile globally antitone despite y(·) being even in r; * Φ(y(α·(r − √n/2))) otherwise — the weight at the cube's inner radius.", DescribeRole.Definition),
            Node("claim-16", "profile_antitone", "profile antitone",
                "The profile is globally antitone — the hypothesis Lemma43B.dom_of_antitone needs.", DescribeRole.Theorem),
            Node("claim-17", "measurable_profile_uncurry", "measurable profile uncurry",
                "hgmeas, discharged. (t, r) ↦ profile a₀ α W n t r is jointly measurable: it is a two-branch if over measurable sets, with PhiC ∘ y(·) measurable on the last branch.", DescribeRole.Theorem),
            Node("claim-18", "measurable_profile_time", "measurable profile time",
                "Fixing the radius leaves a measurable function of t.", DescribeRole.Theorem),
            Node("claim-19", "measurable_profile_radius", "measurable profile radius",
                "Fixing the time leaves a measurable function of r.", DescribeRole.Theorem),
            Node("claim-21", "integrableOn_profile_time", "integrable On profile time",
                "hgt, at the concrete profile. Bounded by Φ ≤ 1/2 on a finite-measure interval.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
