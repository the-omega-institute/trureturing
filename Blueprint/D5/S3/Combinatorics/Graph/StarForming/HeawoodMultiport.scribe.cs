using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodMultiportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual second-cut local obstruction", H("The actual second-cut local obstruction"),
        Blocks(Paragraph(Text("The original thirty-four-vertex adjacency rows, twenty-set, color data, cut edges and finite certificates are retained. The actual graph is bipartite of maximum degree three and the actual twenty-set is dissociation, refuting its proposed cap nineteen. This is a local second-cut obstruction and does not refute global compensation or assert beta exactly twenty.")),
            Node("rows", "rows", "Exact declaration: def rows : List (List Nat).", DescribeRole.Definition),
            Node("adjacency", "adjacency", "Exact declaration: def adjacency (first second : Fin 34) : Prop.", DescribeRole.Definition),
            Node("chosen", "chosen", "Exact declaration: def chosen : List Nat.", DescribeRole.Definition),
            Node("selected", "selected", "Exact declaration: def selected (vertex : Fin 34) : Prop.", DescribeRole.Definition),
            Node("selectedDegree", "selectedDegree", "Exact declaration: def selectedDegree (vertex : Fin 34) : Nat.", DescribeRole.Definition),
            Node("unjoined", "unjoined", "Exact declaration: def unjoined (first second : Fin 34) : Prop.", DescribeRole.Definition),
            Node("color", "color", "Exact declaration: def color (vertex : Fin 34) : Nat.", DescribeRole.Definition),
            Node("witness_dissociates", "witness dissociates", "Exact declaration: theorem witness_dissociates : Dissociates adjacency selected.", DescribeRole.Theorem),
            Node("witness_cardinality", "witness cardinality", "Exact declaration: theorem witness_cardinality : ((List.finRange 34).filter (fun vertex => decide (selected vertex))).length = 20.", DescribeRole.Theorem),
            Node("simple_subcubic", "simple subcubic", "Exact declaration: theorem simple_subcubic : (∀ vertex, ¬ adjacency vertex vertex) ∧ (∀ first second, adjacency first second ↔ adjacency second first) ∧ (∀ vertex, ((List.finRange 34).filter (fun neighbor => decide (adjacency vertex neighbor))).length ≤ 3).", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite : ∀ first second, adjacency first second → color first ≠ color second.", DescribeRole.Theorem),
            Node("attachment_isolates", "attachment isolates", "Exact declaration: theorem attachment_isolates : ∀ vertex : Fin 34, [12, 13, 20, 28].contains vertex.val = true → selected vertex ∧ ∀ neighbor, unjoined vertex neighbor → ¬ selected neighbor.", DescribeRole.Theorem),
            Node("external_port_profile", "external port profile", "Exact declaration: theorem external_port_profile : (∀ vertex : Fin 34, [15, 16, 24, 32].contains vertex.val = true → selected vertex ∧ selectedDegree vertex = 1) ∧ (∀ vertex : Fin 34, [14, 17].contains vertex.val = true → ¬ selected vertex) ∧ (∀ vertex : Fin 34, ((List.finRange 34).filter (fun neighbor => decide (adjacency vertex neighbor))).length = 2 ↔ [14, 15, 16, 17, 24, 32].contains vertex.val = true).", DescribeRole.Theorem),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 34).", DescribeRole.Definition),
            Node("selectedSet", "selectedSet", "Exact declaration: def selectedSet : Finset (Fin 34).", DescribeRole.Definition),
            Node("graph_class", "graph class", "Exact declaration: theorem graph_class : graph.Colorable 2 ∧ ∀ v, DegreeCapacity.degree graph v ≤ 3.", DescribeRole.Theorem),
            Node("selection", "selection", "Exact declaration: theorem selection : IsKIndependent graph 2 selectedSet ∧ selectedSet.card = 20.", DescribeRole.Theorem),
            Node("claim", "claim", "Exact declaration: def claim : Prop.", DescribeRole.Definition),
            Node("result", "result", "Exact declaration: theorem result : ¬ claim.", DescribeRole.Theorem)), []));
}
