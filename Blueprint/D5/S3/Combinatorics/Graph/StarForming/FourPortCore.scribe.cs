using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class FourPortCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/FourPortCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-length four-port strict loss", H("All-length four-port strict loss"),
        Blocks(Paragraph(Text("The actual periodic twenty-per-cell equality graph loses the two disjoint edges x0-x1 and x2-x3 in one marked cell. Exactly their four endpoints have degree two. The actual cut identity gives the unrestricted twelve-per-cell cap. If either complete cut pair is omitted, attaining the cap would force the complementary pair selected, no selected isolates, and no complementary edges. Restoring the edges then contradicts the original periodic integer weight identity. This proves strict loss at every length, with no restriction at the other pair.")),
            Node("cut", "cut", "Exact declaration: def cut (mark : I) (x y : I × Fin 20) : Prop.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (I × Fin 20).", DescribeRole.Definition),
            Node("ports", "ports", "Exact declaration: def ports (mark : I) : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("degree", "degree", "Exact declaration: theorem degree (e : Equiv.Perm I) (mark : I) (x : I × Fin 20) : DegreeCapacity.degree (graph e mark) x = if x ∈ ports mark then 2 else 3.", DescribeRole.Theorem),
            Node("selected_deficiency", "selected deficiency", "Exact declaration: theorem selected_deficiency (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) : deficiency (graph e mark) 3 D = (D ∩ ports mark).card.", DescribeRole.Theorem),
            Node("exact_identity", "exact identity", "Exact declaration: theorem exact_identity (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) : 5*D.card+4+(isolates (graph e mark) D).card+2*complementEdges (graph e mark) D = 60*Fintype.card I+2*(D ∩ ports mark).card.", DescribeRole.Theorem),
            Node("card_bound", "card bound", "Exact declaration: theorem card_bound (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 12*Fintype.card I.", DescribeRole.Theorem),
            Node("weight", "weight", "Exact declaration: def weight : Fin 20 → ℤ.", DescribeRole.Definition),
            Node("total_weight", "total weight", "Exact declaration: theorem total_weight : (∑ v : I × Fin 20, weight v.2) = 0.", DescribeRole.Theorem),
            Node("weight_balance", "weight balance", "Exact declaration: theorem weight_balance (e : Equiv.Perm I) (x : I × Fin 20) : WeightedBalance.neighborSum (EqualityCore.graph e) (fun v => weight v.2) x + 2*weight x.2 = 0.", DescribeRole.Theorem),
            Node("restored_selected_degree", "restored selected degree", "Exact declaration: theorem restored_selected_degree (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (x : I × Fin 20) : selectedDegree (EqualityCore.graph e) D x = selectedDegree (graph e mark) D x + if x ∈ ports mark ∧ (mark,mate x.2) ∈ D then 1 else 0.", DescribeRole.Theorem),
            Node("pair", "pair", "Exact declaration: def pair (mark : I) (side : Bool) : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("omitted_pair_strict", "omitted pair strict", "Exact declaration: theorem omitted_pair_strict (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D) (side : Bool) (hmiss : Disjoint D (pair mark side)) : D.card+1 ≤ 12*Fintype.card I.", DescribeRole.Theorem)), []));
}
