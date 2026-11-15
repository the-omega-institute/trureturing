using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BipartiteOwnersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bipartite owner maxima", H("Exact bipartite owner maxima"),
        Blocks(Paragraph(Text("For every finite bipartite graph, fixing a subset A of one side gives the actual dissociation completion A plus all zero-neighbor opposite vertices plus one representative for each distinct owner. Restriction gives the matching upper bound, so beta is the finite maximum of |A|+r0+p. For cubic graphs, exact edge and right-degree counts give the integer surplus p-2(r1-p)-r2 and an actual attaining left subset with surplus 3(beta-N). No connectedness or nonempty hypothesis is added.")),
            Node("Owns", "Owns", "Exact declaration: def Owns (A : Finset V) (a r : V) : Prop.", DescribeRole.Definition),
            Node("completion_card", "completion card", "Exact declaration: theorem completion_card (A : Finset V) (hA : ∀ a ∈ A, color a = false) : (completion G color A).card = A.card + (zero G color A).card + (owners G color A).card.", DescribeRole.Theorem),
            Node("completion_dissociation", "completion dissociation", "Exact declaration: theorem completion_dissociation (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (A : Finset V) (hA : ∀ a ∈ A, color a = false) : IsKIndependent G 2 (completion G color A).", DescribeRole.Theorem),
            Node("restriction_upper", "restriction upper", "Exact declaration: theorem restriction_upper (D : Finset V) (hD : IsKIndependent G 2 D) : let A.", DescribeRole.Theorem),
            Node("beta_formula", "beta formula", "Exact declaration: theorem beta_formula (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) : beta G 2 = ((Finset.univ.filter (fun v => color v = false)).powerset.sup (fun A => A.card + (zero G color A).card + (owners G color A).card)).", DescribeRole.Theorem),
            Node("rightCount", "rightCount", "Exact declaration: def rightCount (A : Finset V) (j : ℕ) : ℕ.", DescribeRole.Definition),
            Node("cubic_surplus_identity", "cubic surplus identity", "Exact declaration: theorem cubic_surplus_identity (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ) (hN : (Finset.univ.filter (fun v => color v = true)).card = N) (A : Finset V) (hA : ∀ a ∈ A, color a = false) : 3 * ((A.card : ℤ) + (zero G color A).card + (owners G color A).card - N) = surplus G color A.", DescribeRole.Theorem),
            Node("cubic_surplus_maximum", "cubic surplus maximum", "Exact declaration: theorem cubic_surplus_maximum (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ) (hN : (Finset.univ.filter (fun v => color v = true)).card = N) : ∃ A : Finset V, (∀ a ∈ A, color a = false) ∧ surplus G color A = 3*((beta G 2 : ℤ)-N) ∧ ∀ B : Finset V, (∀ b ∈ B, color b = false) → surplus G color B ≤ surplus G color A.", DescribeRole.Theorem)), []));
}
