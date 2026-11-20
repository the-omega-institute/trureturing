using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-size two-connectivity of actual shared ports", H("All-size two-connectivity of actual shared ports"),
        Blocks(Paragraph(Text("The actual ten-vertex core has local vertex-deletion path certificates. An arbitrary transitive index permutation gives paths after deletion through forward or backward shared-port bridges. Every positive cyclic size is covered; the separate bipartite parameter theorem requires even r.")),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (z : I × Fin 11) : ((graph e).induce {x | x≠z}).Preconnected.", DescribeRole.Theorem),
            Node("preconnected", "preconnected", "Exact declaration: theorem preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Preconnected.", DescribeRole.Theorem),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 11, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 11).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 11, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 11).", DescribeRole.Theorem)), []));
}
