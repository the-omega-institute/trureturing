using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class H0GeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/H0Geometry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual H0 cyclic two-connectivity", H("Actual H0 cyclic two-connectivity"),
        Blocks(Paragraph(Text("The original unchanged H0 graph has checked local parent/rank path certificates after every vertex deletion. Its actual port bridge and symbolic transitive index permutation give connectivity and connectivity after every vertex deletion. All positive cyclic lengths are included; exact seventeen-edge counting separately excludes the singleton restored-edge case.")),
            Node("graph", "graph", "Exact declaration: def graph {I : Type} (e : Equiv.Perm I) : SimpleGraph (I × Fin 10).", DescribeRole.Definition),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 10, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 10).", DescribeRole.Theorem),
            Node("cyclic_two_connected", "cyclic two connected", "Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 10, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 10).", DescribeRole.Theorem)), []));
}
