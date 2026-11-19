using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedRingConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-connectivity of all cyclic closed-high assemblies", H("Two-connectivity of all cyclic closed-high assemblies"),
        Blocks(Paragraph(Text("A finite local parent/rank certificate for the sixty-two-vertex open module is combined with a symbolic arbitrary transitive-permutation orbit argument. Every vertex-deleted graph stays connected. The cyclic specialization covers every positive size, including one and two. Neither connectivity nor the parameter equalities are inferred from a finite list of ring sizes.")),
            Node("module_delete_preconnected", "module delete preconnected", "Exact declaration: theorem module_delete_preconnected (z : Fin 62) : (ClosedModule.graph.induce {a | a≠z}).Preconnected.", DescribeRole.Theorem),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (z : I × Fin 62) : ((graph e).induce {x | x≠z}).Preconnected.", DescribeRole.Theorem),
            Node("preconnected", "preconnected", "Exact declaration: theorem preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Preconnected.", DescribeRole.Theorem),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 62, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 62).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 62, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 62).", DescribeRole.Theorem)), []));
}
