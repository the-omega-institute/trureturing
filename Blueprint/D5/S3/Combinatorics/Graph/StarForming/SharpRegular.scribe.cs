using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SharpRegularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SharpRegular.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sharp regular bipartite graphs", H("Actual sharp regular bipartite graphs"),
        Blocks(Paragraph(Text("For every d at least three the actual finRotate graph has order 4d+2, degree d, a proper bipartition, beta=2d+1 and SF=2d+2. The displayed high classes and hubs are minimal forming. The beta proof uses symbolic neighborhood counts for d at least five, the C4-free threshold at d=3 and eighteen actual uniformly weighted squares at d=4. Two-connectivity, all-degree square weights and broken-edge rings remain separate obligations.")),
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
            Node("beta_graph_ge_five", "beta graph ge five", "Exact declaration: theorem beta_graph_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) : beta (graph next) 2 = 2 * Fintype.card I + 1.", DescribeRole.Theorem),
            Node("cyclic_parameters", "cyclic parameters", "Exact declaration: theorem cyclic_parameters (d : ℕ) (hd : 3 ≤ d) : Fintype.card (Vertex (Fin d)) = 4*d+2 ∧ (graph (finRotate d)).Colorable 2 ∧ (∀ v, DegreeCapacity.degree (graph (finRotate d)) v = d) ∧ beta (graph (finRotate d)) 2 = 2*d+1 ∧ SF (graph (finRotate d)) 2 = 2*d+2.", DescribeRole.Theorem)), []));
}
