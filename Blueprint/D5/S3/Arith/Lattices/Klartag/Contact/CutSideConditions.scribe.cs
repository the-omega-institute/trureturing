using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class CutSideConditionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Cut Side Conditions"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate cut side conditions to the stochastic ellipsoid construction.")),
            Node("claim-1", "card_newActive_le", "card new Active le",
                "card (newActive j) ≤ c₃ on goodCut, for j < K: the newly frozen constraints at step j all sit in C_{j+1}.", DescribeRole.Theorem),
            Node("claim-2", "rrAt", "rr At",
                "rr := 5/⁴√n — the ceiling the increment actually needs, and it decays. At n₁ it is 0.132; the resulting coefficient (1/2 + 2rr)/m² is 0.92 there and tends to 1/2.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
