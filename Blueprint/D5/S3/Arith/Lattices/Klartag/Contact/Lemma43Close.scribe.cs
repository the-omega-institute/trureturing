using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43CloseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Close.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Close"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43close to the stochastic ellipsoid construction.")),
            Node("claim-1", "const_normalise", "const normalise",
                "hgbound_chained's constant in C₁·e^{n²t/8} form. The inner-ball term ρⁿ/(2n) is a constant, not a multiple of the exponential; since e^{n²t/8} ≥ 1 it may be absorbed into C₁.", DescribeRole.Theorem),
            Node("claim-2", "hgbound_normalised", "hgbound normalised",
                "The same, in the ENNReal.ofReal form hgbound is stated in.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
