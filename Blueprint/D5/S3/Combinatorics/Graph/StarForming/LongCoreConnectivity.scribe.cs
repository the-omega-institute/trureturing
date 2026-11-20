using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-length two-connectivity of the actual long-core assembly", H("All-length two-connectivity of the actual long-core assembly"),
        Blocks(Paragraph(Text("The open sixty-two-vertex local module retains actual vertex-deletion paths. The H5-to-next-H0 bridge and symbolic transitive permutation give two-connectivity at every positive cyclic length, including one and two. This is the source long-core graph with both crossing seams and is distinct from the closed-high Z family.")),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 62, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 62).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 62, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 62).", DescribeRole.Theorem)), []));
}
