using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class RegularCompensationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph-wide degree and gap compensation", H("Graph-wide degree and gap compensation"),
        Blocks(Paragraph(Text("The actual augmented exchanges combine with the checked finite degree-capacity sum. The degree-weighted inequality applies to every finite bipartite graph with a maximum degree bound; minimum and maximum degrees give the displayed SF bound. Actual finite attainment then yields (2d+1)SF<=dn+2 beta for regular bipartite graphs. For positive d the canonical gap is at most floor(n/(4d+2)). The exact augmented regular remainder identity is proved; no equality partition or extremal construction is inferred from its algebra alone.")),
            Node("weighted_selection_bound", "weighted selection bound", "Exact declaration: theorem weighted_selection_bound (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, DegreeCapacity.degree G v ≤ D) : (∑ v ∈ S, DegreeCapacity.degree G v) + (D + 1) * S.card ≤ D * Fintype.card V + 2 * beta G 2.", DescribeRole.Theorem),
            Node("min_max_selection_bound", "min max selection bound", "Exact declaration: theorem min_max_selection_bound (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (delta D : ℕ) (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v) (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) : (delta + D + 1) * S.card ≤ D * Fintype.card V + 2 * beta G 2.", DescribeRole.Theorem),
            Node("sf_min_max_bound", "sf min max bound", "Exact declaration: theorem sf_min_max_bound (hG : G.Colorable 2) (delta D : ℕ) (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v) (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) : (delta + D + 1) * SF G 2 ≤ D * Fintype.card V + 2 * beta G 2.", DescribeRole.Theorem),
            Node("sf_regular_bound", "sf regular bound", "Exact declaration: theorem sf_regular_bound (hG : G.Colorable 2) (d : ℕ) (hregular : ∀ v, DegreeCapacity.degree G v = d) : (2 * d + 1) * SF G 2 ≤ d * Fintype.card V + 2 * beta G 2.", DescribeRole.Theorem),
            Node("sf_sub_beta_bound", "sf sub beta bound", "Exact declaration: theorem sf_sub_beta_bound (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : (4 * d + 2) * (SF G 2 - beta G 2) ≤ Fintype.card V.", DescribeRole.Theorem),
            Node("sf_sub_beta_floor", "sf sub beta floor", "Exact declaration: theorem sf_sub_beta_floor (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : SF G 2 - beta G 2 ≤ Fintype.card V / (4 * d + 2).", DescribeRole.Theorem),
            Node("regular_remainder", "regular remainder", "Exact declaration: theorem regular_remainder (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) : (d : ℤ) * Fintype.card V + 2 * beta G 2 - (2 * d + 1) * S.card = ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color false).card) + ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color true).card) + ((d : ℤ) * Fintype.card V - (2 * d - 1) * S.card - (DegreeCapacity.isolates G S).card).", DescribeRole.Theorem),
            Node("linear_equality_iff", "linear equality iff", "Exact declaration: theorem linear_equality_iff (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : d * Fintype.card V + 2 * beta G 2 = (2 * d + 1) * S.card ↔ ((2 * d - 1) * S.card + (DegreeCapacity.isolates G S).card = d * Fintype.card V) ∧ (BipartiteExchange.exchange G S hS color false).card = beta G 2 ∧ (BipartiteExchange.exchange G S hS color true).card = beta G 2.", DescribeRole.Theorem)), []));
}
