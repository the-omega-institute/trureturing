using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class FiberConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connectivity through actual connected fibers", H("Connectivity through actual connected fibers"),
        Blocks(Paragraph(Text("Actual inter-fiber edges and connected fibers lift preconnectedness from an arbitrary base graph. Two disjoint endpoint pairs survive every one-vertex deletion, and a strictly decreasing parent rank supplies actual paths to a root. These lemmas are consumed by the reciprocal Heawood assembly.")),
            Node("preconnected_of_fibers", "preconnected of fibers", "Exact declaration: theorem preconnected_of_fibers {V I : Type*} (G : SimpleGraph V) (Q : SimpleGraph I) (f : V → I) (hQ : Q.Preconnected) (hf : ∀ a b, f a = f b → G.Reachable a b) (he : ∀ i j, Q.Adj i j → ∃ a b, f a = i ∧ f b = j ∧ G.Adj a b) : G.Preconnected.", DescribeRole.Theorem),
            Node("surviving_pair", "surviving pair", "Exact declaration: theorem surviving_pair {V : Type*} (a b c d z : V) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : (a ≠ z ∧ b ≠ z) ∨ (c ≠ z ∧ d ≠ z).", DescribeRole.Theorem),
            Node("preconnected_of_rank", "preconnected of rank", "Exact declaration: theorem preconnected_of_rank {V : Type*} (G : SimpleGraph V) (root : V) (parent : V → V) (rank : V → ℕ) (hstep : ∀ v, v ≠ root → G.Adj v (parent v) ∧ rank (parent v) < rank v) : G.Preconnected.", DescribeRole.Theorem)), []));
}
