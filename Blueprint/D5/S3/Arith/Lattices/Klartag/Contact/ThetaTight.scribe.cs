using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ThetaTightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Theta Tight"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate theta tight to the stochastic ellipsoid construction.")),
            Node("claim-1", "alpha_mul_rhoC", "alpha mul rho C",
                "α·ρ = (√a₀)⁻¹ + α√n/2 — the α-dependence of ρ is exactly one factor of α⁻¹.", DescribeRole.Theorem),
            Node("claim-2", "alpha_mul_rhoC_le", "alpha mul rho C le",
                "The upper end of α·ρ, from the tiling defect n·(α√n/2) ≤ 1/4.", DescribeRole.Theorem),
            Node("claim-3", "thetaTight", "theta Tight",
                "The tight threshold. Params.markov asks for 2(p−1)·n·κ_n·C < θ·(pⁿ−1); this is the smallest θ that meets it, written out. Unlike 16·C it is α-free to within the tiling defect, because n·κ_n·C1c = p^{n−1}·(n·αⁿ·C1c).", DescribeRole.Definition),
            Node("claim-4", "two_mul_lt_thetaTight_mul", "two mul lt theta Tight mul",
                "thetaTight clears markov's bound with a factor of two to spare.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
