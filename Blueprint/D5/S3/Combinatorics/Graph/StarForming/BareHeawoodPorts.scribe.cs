using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BareHeawoodPortsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Failure shapes at bare boundary ports", H("Failure shapes at bare boundary ports"),
        Blocks(Paragraph(Text("When an internal deletion failure has no internal supporting explanation, its boundary support forces the displayed bare-port conditions. The companion theorem identifies omitted internal neighbors. These generic statements are not the finite Fano inequality |C|+t<=8, which requires the separate complete local case proof.")),
            Node("only_failure_forces_bare_boundary", "only failure forces bare boundary", "Exact declaration: theorem only_failure_forces_bare_boundary {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted port support : Vertex) (hminimal : Minimal adjacency selection) (hdeleted : selection deleted) (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) (hother : ∀ outside, ¬ selection outside → outside ≠ port → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) (hsupport : selection support) (hkeep : support ≠ deleted) (hedge : adjacency port support) (hnotdeleted : ¬ adjacency port deleted) : ¬ selection port ∧ ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support.", DescribeRole.Theorem),
            Node("internal_neighbors_omitted", "internal neighbors omitted", "Exact declaration: theorem internal_neighbors_omitted {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection internal : Vertex → Prop) (port support : Vertex) (hboundary : ¬ selection port ∧ ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support) (hexternal : ¬ internal support) : ¬ selection port ∧ ∀ neighbor, internal neighbor → adjacency port neighbor → ¬ selection neighbor.", DescribeRole.Theorem)), []));
}
