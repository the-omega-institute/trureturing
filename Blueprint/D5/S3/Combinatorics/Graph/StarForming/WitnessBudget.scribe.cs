using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class WitnessBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual high-witness payments and regular equality resources", H("Actual high-witness payments and regular equality resources"),
        Blocks(Paragraph(Text("Each high vertex pays its selected-degree demand to its actual injective deletion witness. Pointwise payment is bounded by the unused selected-degree capacity and sums to every high demand exactly once. The resulting exact regular budget retains selected isolates and nonnegative pointwise residuals. Equality exhausts every outside resource: every unpaid outside vertex has full selected degree, and high owners split into degree d minus one with an adjacent two-neighbor witness or degree d with a nonadjacent one-neighbor witness. This is an actual graph extraction. The additional complete leaf bijections, class balances, component path normal forms and Heawood block credits require their separate proofs and are not asserted here.")),
            Node("payment_le_capacity", "payment le capacity", "Exact declaration: theorem payment_le_capacity (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) : payment G S hS x ≤ d-selectedDegree G S x.", DescribeRole.Theorem),
            Node("payment_sum", "payment sum", "Exact declaration: theorem payment_sum : ∑ x ∈ Finset.univ \\ S, payment G S hS x = ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v-1).", DescribeRole.Theorem),
            Node("payment_add_unused", "payment add unused", "Exact declaration: theorem payment_add_unused (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) : payment G S hS x + unused G S hS d x = d-selectedDegree G S x.", DescribeRole.Theorem),
            Node("regular_budget", "regular budget", "Exact declaration: theorem regular_budget (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) : (2*d-1)*S.card + (isolates G S).card + (∑ x ∈ Finset.univ \\ S, unused G S hS d x) = d*Fintype.card V.", DescribeRole.Theorem),
            Node("payment_at_witness", "payment at witness", "Exact declaration: theorem payment_at_witness (v : V) (hv : v ∈ CertificateBound.high G S) : payment G S hS (BipartiteExchange.witness G S hS v) = selectedDegree G S v-1.", DescribeRole.Theorem),
            Node("payment_off_image", "payment off image", "Exact declaration: theorem payment_off_image (x : V) (hx : ¬ ∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) : payment G S hS x=0.", DescribeRole.Theorem),
            Node("tight_iff_pointwise", "tight iff pointwise", "Exact declaration: theorem tight_iff_pointwise (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V ↔ ∀ x ∈ Finset.univ \\ S, unused G S hS d x=0.", DescribeRole.Theorem),
            Node("tight_outside_classes", "tight outside classes", "Exact declaration: theorem tight_outside_classes (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) : (∀ v ∈ CertificateBound.high G S, selectedDegree G S v+selectedDegree G S (BipartiteExchange.witness G S hS v)=d+1) ∧ (∀ x ∈ Finset.univ \\ S, (∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) ∨ selectedDegree G S x=d).", DescribeRole.Theorem),
            Node("tight_witness_classes", "tight witness classes", "Exact declaration: theorem tight_witness_classes (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : let x.", DescribeRole.Theorem)), []));
}
