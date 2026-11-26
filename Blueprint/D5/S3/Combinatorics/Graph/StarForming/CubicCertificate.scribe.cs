using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CubicCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rewiring away from selected vertices", H("Rewiring away from selected vertices"),
        Blocks(Paragraph(Text("Rewiring edges whose endpoints are both outside the fixed selection preserves formation for every smaller selection and therefore inclusion-minimality. The arbitrary vertex type and the agreement condition remain explicit. The Fano incidence table, eight-set and deletion witnesses belong with their exact maxima and refutation in HeawoodParameters.")),
            Node("forms_rewiring", "forms rewiring", "Exact declaration: theorem forms_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection smaller : Vertex → Prop) (hsubset : ∀ vertex, smaller vertex → selection vertex) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hforms : Forms original smaller) : Forms modified smaller.", DescribeRole.Theorem),
            Node("minimal_rewiring_forward", "minimal rewiring forward", "Exact declaration: theorem minimal_rewiring_forward {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hminimal : Minimal original selection) : Minimal modified selection.", DescribeRole.Theorem),
            Node("minimal_rewiring", "minimal rewiring", "Exact declaration: theorem minimal_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) : Minimal original selection ↔ Minimal modified selection.", DescribeRole.Theorem)), []));
}
