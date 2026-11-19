using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class PaddingConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/PaddingConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-connectivity of independently sized padding modules and rings", H("Two-connectivity of independently sized padding modules and rings"),
        Blocks(Paragraph(Text("The actual twenty-vertex unmarked core and thirty-four-vertex marked fiber have checked vertex-deletion paths. The projection records each actual fiber, including independently varying core types. Its symbolic transitive-permutation proof gives connectivity and connectivity after every vertex deletion for each positive module and each positive cyclic ring. Singleton restoration and independently varying positive core sizes remain in scope; no finite list of sizes replaces this proof.")),
            Node("core_parent_facts", "core parent facts", "Exact declaration: theorem core_parent_facts : ∀ z a : Fin 20, a≠z → core_parent z a≠z ∧ (a=core_root z ∨ coreGraph.Adj a (core_parent z a) ∧ core_rank z (core_parent z a)<core_rank z a).", DescribeRole.Theorem),
            Node("marked_parent_facts", "marked parent facts", "Exact declaration: theorem marked_parent_facts : ∀ z a : Fin 34, a≠z → marked_parent z a≠z ∧ (a=marked_root z ∨ markedGraph.Adj a (marked_parent z a) ∧ marked_rank z (marked_parent z a)<marked_rank z a).", DescribeRole.Theorem),
            Node("mapped_deleted_reachable", "mapped deleted reachable", "Exact declaration: theorem mapped_deleted_reachable {A V : Type*} (B : SimpleGraph A) (G : SimpleGraph V) (hB : B.Preconnected) (hd : ∀ z, (B.induce {a | a≠z}).Preconnected) (f : A ↪ V) (hf : ∀ a b, B.Adj a b → G.Adj (f a) (f b)) (z : V) (a b : A) (ha : f a≠z) (hb : f b≠z) : (G.induce {x | x≠z}).Reachable ⟨f a,ha⟩ ⟨f b,hb⟩.", DescribeRole.Theorem),
            Node("module_two_connected", "module two connected", "Exact declaration: theorem module_two_connected (e : Equiv.Perm I) (mark : I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e mark).Connected ∧ (∀ z : Vertex I, ((graph e mark).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Vertex I).", DescribeRole.Theorem),
            Node("rings_two_connected", "rings two connected", "Exact declaration: theorem rings_two_connected [Nonempty J] (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) (hq : ∀ j, ∀ a b, ∃ n : ℕ, (q j : K j → K j)^[n] a=b) (he : ∀ i j, ∃ n : ℕ, (e : J → J)^[n] i=j) : (PaddingRings.graph q mark e).Connected ∧ (∀ z : PaddingRings.Vertex K, ((PaddingRings.graph q mark e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (PaddingRings.Vertex K).", DescribeRole.Theorem)), []));
}
