using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CyclicProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CyclicProjection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic connectivity for independently varying fibers", H("Cyclic connectivity for independently varying fibers"),
        Blocks(Paragraph(Text("An actual projection partitions vertices into possibly different fiber types and sizes. Actual entrance and exit vertices and one cyclic bridge per index join connected fibers. After any vertex deletion, local surviving-fiber reachability and distinct entrance and exit ports allow one of the two cyclic directions to reach the deleted fiber. The argument is symbolic over a transitive permutation; it enumerates no graph orders.")),
            Node("preconnected", "preconnected", "Exact declaration: theorem preconnected (G : SimpleGraph V) (f : V → I) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i) (hlocal : ∀ a b, f a=f b → G.Reachable a b) (hbridge : ∀ i, G.Adj (p i) (q (e i))) : G.Preconnected.", DescribeRole.Theorem),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (G : SimpleGraph V) (f : V → I) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i) (hne : ∀ i, p i≠q i) (z : V) (hlocal : ∀ a b : {x : V // x≠z}, f a.val=f b.val → (G.induce {x | x≠z}).Reachable a b) (hbridge : ∀ i, G.Adj (p i) (q (e i))) : (G.induce {x | x≠z}).Preconnected.", DescribeRole.Theorem)), []));
}
