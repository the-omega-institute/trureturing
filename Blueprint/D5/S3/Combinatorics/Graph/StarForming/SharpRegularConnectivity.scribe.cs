using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SharpRegularConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-degree two-connectivity of the sharp positive-gap graphs", H("All-degree two-connectivity of the sharp positive-gap graphs"),
        Blocks(Paragraph(Text("The actual high crown is connected after every vertex deletion by explicit short paths, including a detour when a common opposite high is the deleted vertex. The actual disjoint high--outside--outside--high ears and the two hubs each retain a path into that crown. For every finite index permutation with no fixed point and no two-step fixed point this proves two-connectivity. The cyclic specialization includes every degree at least three, without enumerating graph orders. The separate rings of broken sharp blocks still need their own source integration.")),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I) (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) (z : Vertex I) : ((graph next).induce {v | v ≠ z}).Preconnected.", DescribeRole.Theorem),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I) (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) : (graph next).Connected ∧ (∀ z : Vertex I, ((graph next).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex I).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (d : ℕ) (hd : 3 ≤ d) : (graph (finRotate d)).Connected ∧ (∀ z : Vertex (Fin d), ((graph (finRotate d)).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex (Fin d)).", DescribeRole.Theorem)), []));
}
