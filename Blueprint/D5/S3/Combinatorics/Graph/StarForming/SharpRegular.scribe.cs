using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SharpRegularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SharpRegular.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sharp regular bipartite graphs", H("Actual sharp regular bipartite graphs"),
        Blocks(Paragraph(Text("The graph has two bipartition sides, each consisting of a high class, an outside class and one hub. An arbitrary fixed-point-free permutation determines the two excluded outside incidences. Symbolic neighbor counts prove degree d, the actual high classes and hubs form a minimal selection of size 2d+2, and degree capacity proves SF exactly 2d+2 for d at least three. Actual crown and outside-neighbor counting proves beta exactly 2d+1 for d at least five. The cyclic d=3,4 boundaries, two-connectivity, all-degree square weights and broken-edge rings are separate obligations.")),
            Node("Side", "Side", "Exact declaration: abbrev Side (I : Type).", DescribeRole.Definition),
            Node("Vertex", "Vertex", "Exact declaration: abbrev Vertex (I : Type).", DescribeRole.Definition),
            Node("link", "link", "Exact declaration: def link (next : Equiv.Perm I) : Side I → Side I → Prop | none,none => False | none,some (k,_) => k = true | some (k,_),none => k = true | some (false,i),some (false,j) => i ≠ j | some (false,i),some (true,j) => i = j | some (true,i),some (false,j) => i = j | some (true,i),some (true,j) => j ≠ next i ∧ j ≠ next (next i) instance (next : Equiv.Perm I) : DecidableRel (link next).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (Vertex I).", DescribeRole.Definition),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2.", DescribeRole.Theorem),
            Node("regular", "regular", "Exact declaration: theorem regular (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i) (v : Vertex I) : DegreeCapacity.degree (graph next) v = Fintype.card I.", DescribeRole.Theorem),
            Node("selected", "selected", "Exact declaration: def selected : Side I → Prop | none => True | some (k,_) => k = false instance : DecidablePred (@selected I).", DescribeRole.Definition),
            Node("selection", "selection", "Exact declaration: def selection : Finset (Vertex I).", DescribeRole.Definition),
            Node("selection_minimal", "selection minimal", "Exact declaration: theorem selection_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 selection.", DescribeRole.Theorem),
            Node("selection_card", "selection card", "Exact declaration: theorem selection_card : (selection : Finset (Vertex I)).card = 2 * Fintype.card I + 2.", DescribeRole.Theorem),
            Node("sf_graph", "sf graph", "Exact declaration: theorem sf_graph (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i) (hd : 3 ≤ Fintype.card I) : SF (graph next) 2 = 2 * Fintype.card I + 2.", DescribeRole.Theorem),
            Node("dissociation_cap_ge_five", "dissociation cap ge five", "Exact declaration: theorem dissociation_cap_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) (D : Finset (Vertex I)) (hD : IsKIndependent (graph next) 2 D) : D.card ≤ 2 * Fintype.card I + 1.", DescribeRole.Theorem),
            Node("beta_graph_ge_five", "beta graph ge five", "Exact declaration: theorem beta_graph_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) : beta (graph next) 2 = 2 * Fintype.card I + 1.", DescribeRole.Theorem)), []));
}
