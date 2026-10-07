using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43ParamsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Params"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43params to the stochastic ellipsoid construction.")),
            Node("claim-1", "params_a0_ge_one", "params a0 ge one",
                "a₀ = (1 − 1/n)⁻¹² ≥ 1 for n ≥ 2. ha₀ of hgbound_chained.", DescribeRole.Theorem),
            Node("claim-3", "a0_ge_one", "a0 ge one",
                "Params' inherits a₀ ≥ 1.", DescribeRole.Theorem),
            Node("claim-4", "window_sub_pos", "window sub pos",
                "The extended radial parameters ensure that a0-sqrt(T)*y stays positive throughout the substitution window.", DescribeRole.Theorem),
            Node("claim-5", "window_one_sub_pos", "window one sub pos",
                "The window smallness condition keeps 1-sqrt(T)*y positive throughout the substitution window.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
