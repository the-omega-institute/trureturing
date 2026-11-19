using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class TripleConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/TripleConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-positive-length triple-port two-connectivity", H("All-positive-length triple-port two-connectivity"),
        Blocks(Paragraph(Text("Actual checked local vertex-deletion paths and the sixteen-to-seventeen bridge combine with the symbolic orbit argument. For every positive cyclic length the actual triple-port assembly is connected and remains connected after deleting any vertex. The proof includes lengths one and two.")),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 48, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 48).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 48, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 48).", DescribeRole.Theorem)), []));
}
