using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CyclicConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cyclic bridges and vertex-deleted fibers", H("Actual cyclic bridges and vertex-deleted fibers"),
        Blocks(Paragraph(Text("Local actual graph paths and a transitive permutation give full connectivity. With distinct bridge ports and each local vertex deletion connected, an appropriate forward or inverse cyclic route avoids the deleted bridge endpoint. This general path lemma is consumed by the actual H0 and long-core family proofs.")),
            Node("preconnected", "preconnected", "Exact declaration: theorem preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : A) (hB : B.Preconnected) (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b)) (hbridge : ∀ i, G.Adj (i,p) (e i,q)) : G.Preconnected.", DescribeRole.Theorem),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A) (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (p q : A) (hpq : p≠q) (hB : B.Preconnected) (hdelete : ∀ z : A, (B.induce {a | a≠z}).Preconnected) (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b)) (hbridge : ∀ i, G.Adj (i,p) (e i,q)) (z : I × A) : (G.induce {x | x≠z}).Preconnected.", DescribeRole.Theorem)), []));
}
