using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BinaryLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BinaryLift.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual binary voltage covers", H("Actual binary voltage covers"),
        Blocks(Paragraph(Text("A symmetric binary voltage on actual base edges defines the actual two-sheet graph. Vertex switches and the deck flip are graph isomorphisms. Projection is locally bijective. Over a preconnected base with an explicit vertex, the lift is preconnected exactly when the voltage is not a vertex coboundary. No finite list of base graphs or cover sizes is assumed.")),
            Node("F2", "F2", "Exact declaration: abbrev F2.", DescribeRole.Definition),
            Node("Voltage", "Voltage", "Exact declaration: structure Voltage.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (s : Voltage G) : SimpleGraph (V × F2).", DescribeRole.Definition),
            Node("switched", "switched", "Exact declaration: def switched (s : Voltage G) (t : V → F2) : Voltage G.", DescribeRole.Definition),
            Node("switchIso", "switchIso", "Exact declaration: def switchIso (s : Voltage G) (t : V → F2) : graph G s ≃g graph G (switched G s t).", DescribeRole.Definition),
            Node("flipIso", "flipIso", "Exact declaration: def flipIso (s : Voltage G) : graph G s ≃g graph G s.", DescribeRole.Definition),
            Node("cover", "cover", "Exact declaration: theorem cover (s : Voltage G) : CoverPullback.NeighborhoodCover G.Adj (graph G s).Adj Prod.fst.", DescribeRole.Theorem),
            Node("preconnected_iff", "preconnected iff", "Exact declaration: theorem preconnected_iff (s : Voltage G) (hG : G.Preconnected) (r : V) : (graph G s).Preconnected ↔ ¬ ∃ t : V → F2, ∀ v w, G.Adj v w → s.sign v w=t v+t w.", DescribeRole.Theorem)), []));
}
