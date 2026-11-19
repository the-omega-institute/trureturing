using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DegreeCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global finite degree capacity", H("Global finite degree capacity"),
        Blocks(Paragraph(Text("For every finite simple graph and every minimal two-star-forming S, the sum of ambient degrees on S plus the number of selected isolates is at most |S| plus Delta times the outside cardinality. This is the integer sum(deg-1)+z form without natural-number truncation. The chosen high-vertex failure map is injective, the actual outside capacity is summed only once, and the cut is counted on both sides. For d-regular graphs with d at least one, (2d-1)|S|+z<=d|V|, hence SF two<=floor(d|V|/(2d-1)). No equality classification, extremal construction or sharp compensation theorem is inferred from this upper bound alone.")),
            Node("degree", "degree", "Exact declaration: def degree (v : V) : ℕ.", DescribeRole.Definition),
            Node("selectedDegree", "selectedDegree", "Exact declaration: def selectedDegree (S : Finset V) (v : V) : ℕ.", DescribeRole.Definition),
            Node("isolates", "isolates", "Exact declaration: def isolates (S : Finset V) : Finset V.", DescribeRole.Definition),
            Node("failure_selected_degree_le_two", "failure selected degree le two", "Exact declaration: theorem failure_selected_degree_le_two (S : Finset V) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) : selectedDegree G S x ≤ 2.", DescribeRole.Theorem),
            Node("adjacent_failure_degree", "adjacent failure degree", "Exact declaration: theorem adjacent_failure_degree (S : Finset V) (D : ℕ) (hD : ∀ v, degree G v ≤ D) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) (hedge : G.Adj x v) : selectedDegree G S v + 1 ≤ D.", DescribeRole.Theorem),
            Node("witness_degree_capacity", "witness degree capacity", "Exact declaration: theorem witness_degree_capacity (S : Finset V) (D : ℕ) (hD : ∀ v, degree G v ≤ D) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) : selectedDegree G S v + selectedDegree G S x ≤ D + 1.", DescribeRole.Theorem),
            Node("high_capacity_sum", "high capacity sum", "Exact declaration: theorem high_capacity_sum (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, degree G v ≤ D) : ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1) ≤ ∑ x ∈ Finset.univ \\ S, (D - selectedDegree G S x).", DescribeRole.Theorem),
            Node("degree_sum_cut", "degree sum cut", "Exact declaration: theorem degree_sum_cut (S : Finset V) : ∑ v ∈ S, degree G v = (∑ v ∈ S, selectedDegree G S v) + ∑ x ∈ Finset.univ \\ S, selectedDegree G S x.", DescribeRole.Theorem),
            Node("selected_degree_identity", "selected degree identity", "Exact declaration: theorem selected_degree_identity (S : Finset V) : (∑ v ∈ S, selectedDegree G S v) + (isolates G S).card = S.card + ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1).", DescribeRole.Theorem),
            Node("degree_capacity", "degree capacity", "Exact declaration: theorem degree_capacity (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, degree G v ≤ D) : (∑ v ∈ S, degree G v) + (isolates G S).card ≤ S.card + D * (Finset.univ \\ S).card.", DescribeRole.Theorem),
            Node("regular_selection_bound", "regular selection bound", "Exact declaration: theorem regular_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) : (2 * d - 1) * S.card + (isolates G S).card ≤ d * Fintype.card V.", DescribeRole.Theorem),
            Node("sf_regular_bound", "sf regular bound", "Exact declaration: theorem sf_regular_bound (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) : SF G 2 ≤ d * Fintype.card V / (2 * d - 1).", DescribeRole.Theorem),
            Node("min_max_selection_bound", "min max selection bound", "Exact declaration: theorem min_max_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S) (delta D : ℕ) (hpositive : 2 ≤ delta + D) (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) : (delta + D - 1) * S.card + (isolates G S).card ≤ D * Fintype.card V.", DescribeRole.Theorem),
            Node("sf_min_max_bound", "sf min max bound", "Exact declaration: theorem sf_min_max_bound (delta D : ℕ) (hpositive : 2 ≤ delta + D) (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) : SF G 2 ≤ D * Fintype.card V / (delta + D - 1).", DescribeRole.Theorem),
            Node("dissociation_cut_bound", "dissociation cut bound", "Exact declaration: theorem dissociation_cut_bound (S : Finset V) (hS : IsKIndependent G 2 S) : 2 * (∑ v ∈ S, degree G v) ≤ S.card + ∑ v : V, degree G v.", DescribeRole.Theorem),
            Node("dissociation_deficiency_bound", "dissociation deficiency bound", "Exact declaration: theorem dissociation_deficiency_bound (S : Finset V) (hS : IsKIndependent G 2 S) (d : ℕ) (hd : 1 ≤ d) (hmax : ∀ v, degree G v ≤ d) : (2 * d - 1) * S.card + (∑ v : V, (d - degree G v)) ≤ d * Fintype.card V + 2 * (∑ v ∈ S, (d - degree G v)).", DescribeRole.Theorem)), []));
}
