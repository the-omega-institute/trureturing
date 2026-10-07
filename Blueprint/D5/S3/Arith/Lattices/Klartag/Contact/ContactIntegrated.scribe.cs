using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ContactIntegratedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Contact Integrated"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate contact integrated to the stochastic ellipsoid construction.")),
            Node("claim-2", "integral_card_eq", "integral card eq",
                "The expected contact count at one step is the window sum of per-time contact probabilities.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
