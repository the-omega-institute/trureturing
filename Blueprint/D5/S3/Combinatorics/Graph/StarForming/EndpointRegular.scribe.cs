using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class EndpointRegularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-degree order-bound equality graphs", H("All-degree order-bound equality graphs"),
        Blocks(Paragraph(Text("The source four independent parts have sizes d,d,d-1,d-1, a matching between the selected parts, and complete incidence to the opposite omitted parts. Exact neighborhoods give regularity, the actual matching selection attains two d, and the general regular degree bound gives beta two and SF two both equal two d. Explicit deletion paths prove two-connectivity for every d at least two, including the degree-two C6 detour. The parameter theorem includes degree one as a single edge. This construction has order four d minus two and is separate from the positive-gap graphs of order four d plus two.")),
            Node("Side", "Side", "Exact declaration: abbrev Side (d : ℕ).", DescribeRole.Definition),
            Node("Vertex", "Vertex", "Exact declaration: abbrev Vertex (d : ℕ).", DescribeRole.Definition),
            Node("link", "link", "Exact declaration: def link {d : ℕ} : Side d → Side d → Prop | .inl i, .inl j => i = j | .inl _, .inr _ => True | .inr _, .inl _ => True | .inr _, .inr _ => False instance {d : ℕ} : DecidableRel (@link d).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (d : ℕ) : SimpleGraph (Vertex d).", DescribeRole.Definition),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (d : ℕ) : (graph d).Colorable 2.", DescribeRole.Theorem),
            Node("regular", "regular", "Exact declaration: theorem regular (d : ℕ) (hd : 1 ≤ d) (v : Vertex d) : DegreeCapacity.degree (graph d) v = d.", DescribeRole.Theorem),
            Node("matching", "matching", "Exact declaration: def matching (d : ℕ) : Finset (Vertex d).", DescribeRole.Definition),
            Node("matching_card", "matching card", "Exact declaration: theorem matching_card (d : ℕ) : (matching d).card=2*d.", DescribeRole.Theorem),
            Node("matching_independent", "matching independent", "Exact declaration: theorem matching_independent (d : ℕ) : IsKIndependent (graph d) 2 (matching d).", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (d : ℕ) (hd : 1 ≤ d) : Fintype.card (Vertex d)=4*d-2 ∧ beta (graph d) 2=2*d ∧ SF (graph d) 2=2*d.", DescribeRole.Theorem),
            Node("delete_preconnected", "delete preconnected", "Exact declaration: theorem delete_preconnected (d : ℕ) (hd : 2 ≤ d) (z : Vertex d) : ((graph d).induce {v | v ≠ z}).Preconnected.", DescribeRole.Theorem),
            Node("two_connected", "two connected", "Exact declaration: theorem two_connected (d : ℕ) (hd : 2 ≤ d) : (graph d).Connected ∧ (∀ z : Vertex d, ((graph d).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex d).", DescribeRole.Theorem)), []));
}
