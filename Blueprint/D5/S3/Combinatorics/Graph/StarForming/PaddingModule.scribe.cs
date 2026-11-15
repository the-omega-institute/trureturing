using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class PaddingModuleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/PaddingModule.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arbitrary-size open padding modules", H("Actual arbitrary-size open padding modules"),
        Blocks(Paragraph(Text("The disjoint broken Heawood block and marked four-port equality core form the actual open module. Saturating the Heawood block omits its own first core pair and pays one strictly lost core vertex, while the remaining two ports are unrestricted. The original minimal forming set and dissociation set remain actual attained witnesses. The module has exactly two degree-two ring ports and all other degrees three, with a proper coloring across both attachment edges.")),
            Node("Vertex", "Vertex", "Exact declaration: abbrev Vertex (I : Type).", DescribeRole.Definition),
            Node("adjacency", "adjacency", "Exact declaration: def adjacency (e : Equiv.Perm I) (mark : I) : Vertex I → Vertex I → Prop | .inl v,.inl w => HeawoodPorts.graph.Adj v w | .inr x,.inr y => (FourPortCore.graph e mark).Adj x y | .inl v,.inr y => y.1=mark ∧ ((v=0 ∧ y.2=13) ∨ (v=8 ∧ y.2=12)) | .inr x,.inl w => x.1=mark ∧ ((w=0 ∧ x.2=13) ∨ (w=8 ∧ x.2=12)) def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (Vertex I).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (Vertex I).", DescribeRole.Definition),
            Node("restrictions", "restrictions", "Exact declaration: theorem restrictions (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph e mark) 2 D) : IsKIndependent HeawoodPorts.graph 2 D.toLeft ∧ IsKIndependent (FourPortCore.graph e mark) 2 D.toRight.", DescribeRole.Theorem),
            Node("beta_cap", "beta cap", "Exact declaration: theorem beta_cap (e : Equiv.Perm I) (mark : I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 7+12*Fintype.card I.", DescribeRole.Theorem),
            Node("forming", "forming", "Exact declaration: def forming : Finset (Vertex I).", DescribeRole.Definition),
            Node("independent", "independent", "Exact declaration: def independent : Finset (Vertex I).", DescribeRole.Definition),
            Node("forming_minimal", "forming minimal", "Exact declaration: theorem forming_minimal (e : Equiv.Perm I) (mark : I) : IsMinimalStarForming (graph e mark) 2 forming.", DescribeRole.Theorem),
            Node("forming_card", "forming card", "Exact declaration: theorem forming_card : (forming : Finset (Vertex I)).card=8+12*Fintype.card I.", DescribeRole.Theorem),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (e : Equiv.Perm I) (mark : I) : Vertex I → Finset (Vertex I) | .inl v => (Cubic.brokenNeighbors v).toFinset.map Function.Embedding.inl ∪ (if v=0 then {Sum.inr (mark,13)} else if v=8 then {Sum.inr (mark,12)} else ∅) | .inr x => ((EqualityCore.neighbors e x).filter (fun y => ¬ FourPortCore.cut mark x y)).map Function.Embedding.inr ∪ (if x=(mark,12) then {Sum.inl 8} else if x=(mark,13) then {Sum.inl 0} else ∅) set_option maxHeartbeats 1200000 in theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : Vertex I) : y ∈ neighbors e mark x ↔ (graph e mark).Adj x y.", DescribeRole.Definition),
            Node("mem_neighbors", "mem neighbors", "Exact declaration: theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : Vertex I) : y ∈ neighbors e mark x ↔ (graph e mark).Adj x y.", DescribeRole.Theorem),
            Node("leftPort", "leftPort", "Exact declaration: def leftPort (mark : I) : Vertex I.", DescribeRole.Definition),
            Node("rightPort", "rightPort", "Exact declaration: def rightPort (mark : I) : Vertex I.", DescribeRole.Definition),
            Node("degree", "degree", "Exact declaration: theorem degree (e : Equiv.Perm I) (mark : I) (x : Vertex I) : DegreeCapacity.degree (graph e mark) x = if x=leftPort mark ∨ x=rightPort mark then 2 else 3.", DescribeRole.Theorem),
            Node("color", "color", "Exact declaration: def color : Vertex I → Bool | .inl v => decide (7 ≤ v.val) | .inr x => EqualityCore.color x.2 /-- The actual point/line coloring agrees with the periodic core coloring across both new attachment edges. -/ theorem proper_color (e : Equiv.Perm I) (mark : I) (x y : Vertex I) (h : (graph e mark).Adj x y) : color x ≠ color y.", DescribeRole.Definition),
            Node("proper_color", "proper color", "Exact declaration: theorem proper_color (e : Equiv.Perm I) (mark : I) (x y : Vertex I) (h : (graph e mark).Adj x y) : color x ≠ color y.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (e : Equiv.Perm I) (mark : I) : (graph e mark).Colorable 2.", DescribeRole.Theorem),
            Node("independent_valid", "independent valid", "Exact declaration: theorem independent_valid (e : Equiv.Perm I) (mark : I) : IsKIndependent (graph e mark) 2 independent.", DescribeRole.Theorem),
            Node("independent_card", "independent card", "Exact declaration: theorem independent_card : (independent : Finset (Vertex I)).card=7+12*Fintype.card I.", DescribeRole.Theorem)), []));
}
