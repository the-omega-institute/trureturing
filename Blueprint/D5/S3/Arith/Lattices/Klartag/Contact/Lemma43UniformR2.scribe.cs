using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43UniformR2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Uniform R2"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform r2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "two_logn_sqrtT_le_gap2", "two logn sqrt T le gap2",
                "At the generic window the reach gap is exactly 1/2, so the split point 2·log n sits below the endpoint by logn_sqrtT_le_quarter alone.", DescribeRole.Theorem),
            Node("claim-2", "hgbound_at2", "hgbound at2",
                "Lemma 4.3 at a single t ≥ 16/n², at the reach window.", DescribeRole.Theorem),
            Node("claim-3", "windowR2_nonneg", "window R2 nonneg",
                "The reach window is nonnegative.", DescribeRole.Theorem),
            Node("claim-5", "radial_bound_of_chain2", "radial bound of chain2",
                "Tonelli integration over the time horizon converts the uniform contact-profile estimate into a radial integral bound. The exact exponential time integral cancels the dimension factors and gives an absolute coefficient.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
