using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class PortClauseOwnershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal clauses at a boundary port", H("Internal clauses at a boundary port"),
        Blocks(Paragraph(Text("A clause based at a selected port includes the actual external neighbor when the graph and support conditions displayed in the theorem hold. The resulting support and private-ownership facts constrain the possible external sole-neighbor witness. The graph relation, internal set, selected set and boundary ports remain separate parameters.")),
            Node("BasedAt", "BasedAt", "Exact declaration: def BasedAt {Vertex : Type} (internal : Vertex → Prop) (port : Vertex) : Clause Vertex → Prop | .closed center => center = port | .oriented center neighbor => (center = port ∧ internal neighbor) ∨ (neighbor = port ∧ internal center) theorem external_neighbor_in_support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal : Vertex → Prop) (port vertex : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hexternal : ¬ internal vertex) (hedge : adjacency port vertex) : Support adjacency clause vertex.", DescribeRole.Definition),
            Node("external_neighbor_in_support", "external neighbor in support", "Exact declaration: theorem external_neighbor_in_support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal : Vertex → Prop) (port vertex : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hexternal : ¬ internal vertex) (hedge : adjacency port vertex) : Support adjacency clause vertex.", DescribeRole.Theorem),
            Node("outside_neighbors_unique", "outside neighbors unique", "Exact declaration: theorem outside_neighbors_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (internal selection : Vertex → Prop) (port owner : Vertex) (clause : Clause Vertex) (hbased : BasedAt internal port clause) (hprivate : Private adjacency selection clause owner) : ∀ vertex, ¬ internal vertex → selection vertex → adjacency port vertex → vertex = owner.", DescribeRole.Theorem)), []));
}
