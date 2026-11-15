using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class PaddingRingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/PaddingRings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual variable-size four-port assemblies", H("Actual variable-size four-port assemblies"),
        Blocks(Paragraph(Text("Every module has its own finite core type, permutation and marked cell. An independent module permutation joins exactly the remaining two degree-two ports. This includes all positive unequal core sizes and singleton seam restoration. Each disjoint actual module pays its own strict loss; the dependent fiber sum proves exact beta and the original forming set attains SF after outside-only rewiring. Structural connectivity requires a separate argument.")),
            Node("Vertex", "Vertex", "Exact declaration: abbrev Vertex.", DescribeRole.Definition),
            Node("Within", "Within", "Exact declaration: inductive Within (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) : Vertex K → Vertex K → Prop | intro (j : J) (v w : PaddingModule.Vertex (K j)) (h : (PaddingModule.graph (q j) (mark j)).Adj v w) : Within q mark ⟨j,v⟩ ⟨j,w⟩ variable {K} private theorem within_same (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (j : J) (v w : PaddingModule.Vertex (K j)) : Within K q mark ⟨j,v⟩ ⟨j,w⟩ ↔ (PaddingModule.graph (q j) (mark j)).Adj v w.", DescribeRole.Definition),
            Node("left", "left", "Exact declaration: def left (mark : ∀ j, K j) (j : J) : Vertex K.", DescribeRole.Definition),
            Node("right", "right", "Exact declaration: def right (mark : ∀ j, K j) (j : J) : Vertex K.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : SimpleGraph (Vertex K).", DescribeRole.Definition),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x : Vertex K) : Finset (Vertex K).", DescribeRole.Definition),
            Node("mem_neighbors", "mem neighbors", "Exact declaration: theorem mem_neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x y : Vertex K) : y ∈ neighbors q mark e x ↔ (graph q mark e).Adj x y.", DescribeRole.Theorem),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (Vertex K)) (j : J) : Finset (PaddingModule.Vertex (K j)).", DescribeRole.Definition),
            Node("card_slices", "card slices", "Exact declaration: theorem card_slices (S : Finset (Vertex K)) : S.card=∑ j, (slice S j).card.", DescribeRole.Theorem),
            Node("beta_upper", "beta upper", "Exact declaration: theorem beta_upper (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : beta (graph q mark e) 2 ≤ 7*Fintype.card J+12*∑ j, Fintype.card (K j).", DescribeRole.Theorem),
            Node("regular", "regular", "Exact declaration: theorem regular (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (x : Vertex K) : DegreeCapacity.degree (graph q mark e) x=3.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : (graph q mark e).Colorable 2.", DescribeRole.Theorem),
            Node("independent", "independent", "Exact declaration: def independent : Finset (Vertex K).", DescribeRole.Definition),
            Node("forming", "forming", "Exact declaration: def forming : Finset (Vertex K).", DescribeRole.Definition),
            Node("independent_valid", "independent valid", "Exact declaration: theorem independent_valid (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : IsKIndependent (graph q mark e) 2 independent.", DescribeRole.Theorem),
            Node("independent_card", "independent card", "Exact declaration: theorem independent_card : (independent : Finset (Vertex K)).card= 7*Fintype.card J+12*∑ j, Fintype.card (K j).", DescribeRole.Theorem),
            Node("forming_card", "forming card", "Exact declaration: theorem forming_card : (forming : Finset (Vertex K)).card= 8*Fintype.card J+12*∑ j, Fintype.card (K j).", DescribeRole.Theorem),
            Node("order", "order", "Exact declaration: theorem order : Fintype.card (Vertex K)=14*Fintype.card J+20*∑ j, Fintype.card (K j).", DescribeRole.Theorem),
            Node("forming_minimal", "forming minimal", "Exact declaration: theorem forming_minimal (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : IsMinimalStarForming (graph q mark e) 2 forming.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) : beta (graph q mark e) 2 = 7*Fintype.card J+12*∑ j, Fintype.card (K j) ∧ SF (graph q mark e) 2 = 8*Fintype.card J+12*∑ j, Fintype.card (K j).", DescribeRole.Theorem)), []));
}
