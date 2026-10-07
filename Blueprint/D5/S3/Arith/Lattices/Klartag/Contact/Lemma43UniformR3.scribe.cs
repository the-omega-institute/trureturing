using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43UniformR3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Uniform R3"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform r3 to the stochastic ellipsoid construction.")),
            Node("claim-1", "integrableOn_radial_terminal2", "integrable On radial terminal2",
                "The terminal summand is integrable. Profile.integrableOn_profile_radial at t = ChainDrift.horizon n and W = WindowR2.windowR2 α n.", DescribeRole.Theorem),
            Node("claim-2", "integrableOn_radial_fR2", "integrable On radial f R2",
                "The integrated summand is integrable, in the 4·∫ shape fR4/fR2 uses.", DescribeRole.Theorem),
            Node("claim-4", "radial_bound_combined_le", "radial bound combined le",
                "The combined radial bound. §2 plus radial_bound4_of_chain2 and radial_bound_terminal2: the constant is a·4·C1R·(8 − 8/n²) + b·C1cR·n², with no new factor and the n² of the exponent still cancelled by the horizon in the first summand.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
