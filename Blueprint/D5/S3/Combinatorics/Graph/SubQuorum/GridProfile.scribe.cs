using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class GridProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact odd-integer grid profiles", H("Exact odd-integer grid profiles"),
        Blocks(Paragraph(Text("The actual path-neighborhood defect is at most one; positive defect forces full alternating support. Finite odd-integer level decomposition proves the complete source profile theorem without a negative-entry lower bound. Exact adjacent-pair summation and odd-ladder rigidity are consumed by the actual rectangular-grid dissociation proof.")),
            Node("three_free_card", "three free card", "Exact declaration: theorem three_free_card (n : ℕ) (P : Finset ℕ) (hP : ∀ i ∈ P, i < n) (hthree : ∀ i, ¬ (i ∈ P ∧ i+1 ∈ P ∧ i+2 ∈ P)) : P.card ≤ n-n/3.", DescribeRole.Theorem),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors {n : ℕ} (P : Finset (Fin n)) : Finset (Fin n).", DescribeRole.Definition),
            Node("card_le_neighbors_of_missing_even", "card le neighbors of missing even", "Exact declaration: theorem card_le_neighbors_of_missing_even {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (pivot : Fin n) (hp : pivot.val % 2 = 0) (hmissing : pivot ∉ P) : P.card ≤ (neighbors P).card.", DescribeRole.Theorem),
            Node("odd_path_defect_support", "odd path defect support", "Exact declaration: theorem odd_path_defect_support {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ (SimpleGraph.pathGraph n).Adj a b) (hdefect : (neighbors P).card < P.card) : ∀ i : Fin n, i ∈ P ↔ i.val % 2 = 0.", DescribeRole.Theorem),
            Node("odd_path_defect_bound", "odd path defect bound", "Exact declaration: theorem odd_path_defect_bound {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) : P.card ≤ (neighbors P).card + 1.", DescribeRole.Theorem),
            Node("even_path_expansion", "even path expansion", "Exact declaration: theorem even_path_expansion {n : ℕ} (hn : n % 2 = 0) (P : Finset (Fin n)) : P.card ≤ (neighbors P).card.", DescribeRole.Theorem),
            Node("Compatible", "Compatible", "Exact declaration: def Compatible {n : ℕ} (a : Fin n → ℤ) : Prop.", DescribeRole.Definition),
            Node("upperLevel", "upperLevel", "Exact declaration: def upperLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n).", DescribeRole.Definition),
            Node("lowerLevel", "lowerLevel", "Exact declaration: def lowerLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n).", DescribeRole.Definition),
            Node("even_level_balance", "even level balance", "Exact declaration: theorem even_level_balance {n : ℕ} (hn : n % 2 = 0) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) : (upperLevel a h).card ≤ (lowerLevel a h).card.", DescribeRole.Theorem),
            Node("odd_level_balance", "odd level balance", "Exact declaration: theorem odd_level_balance {n : ℕ} (hn : n % 2 = 1) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) : (upperLevel a h).card ≤ (lowerLevel a h).card+1.", DescribeRole.Theorem),
            Node("positive_level_forces_alternation", "positive level forces alternation", "Exact declaration: theorem positive_level_forces_alternation {n : ℕ} (hn : n % 2 = 1) (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) (hpos : (lowerLevel a h).card < (upperLevel a h).card) : ∀ i : Fin n, (i.val % 2 = 0 → 0<a i) ∧ (i.val % 2 = 1 → a i<0).", DescribeRole.Theorem),
            Node("profile_level_identity", "profile level identity", "Exact declaration: theorem profile_level_identity {n : ℕ} (a : Fin n → ℤ) (H : ℕ) (hodd : ∀ i, a i%2=1) (hlo : ∀ i, -(2*(H : ℤ)+1) ≤ a i) (hhi : ∀ i, a i ≤ 2*(H : ℤ)+1) : (∑ i, a i) = (∑ i, if 0<a i then (1 : ℤ) else -1) + 2 * ∑ h ∈ Finset.range H, ((upperLevel a h).card - ((lowerLevel a h).card : ℤ)).", DescribeRole.Theorem),
            Node("sign_sum_bound", "sign sum bound", "Exact declaration: theorem sign_sum_bound {n : ℕ} (a : Fin n → ℤ) (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val → ¬ (0<a i ∧ 0<a j ∧ 0<a k)) : (∑ i, if 0<a i then (1 : ℤ) else -1) ≤ (n : ℤ)-2*(n/3 : ℕ).", DescribeRole.Theorem),
            Node("profile_bound", "profile bound", "Exact declaration: theorem profile_bound {n : ℕ} (a : Fin n → ℤ) (A : ℕ) (hA : A%2=1) (hodd : ∀ i, a i%2=1) (hupper : ∀ i, a i ≤ A) (ha : Compatible a) (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val → ¬ (0<a i ∧ 0<a j ∧ 0<a k)) : (∑ i, a i) ≤ if n%2=0 then (n : ℤ)-2*(n/3 : ℕ) else max (A : ℤ) ((n : ℤ)-2*(n/3 : ℕ)).", DescribeRole.Theorem),
            Node("odd_adjacent_sum_bound", "odd adjacent sum bound", "Exact declaration: theorem odd_adjacent_sum_bound {n : ℕ} (hn : n%2=1) (f : Fin n → ℤ) (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2) (pivot : Fin n) (hp : pivot.val%2=0) : (∑ i, f i) ≤ (n : ℤ)-1+f pivot.", DescribeRole.Theorem),
            Node("even_adjacent_sum_bound", "even adjacent sum bound", "Exact declaration: theorem even_adjacent_sum_bound {n : ℕ} (hn : n%2=0) (f : Fin n → ℤ) (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2) : (∑ i, f i) ≤ n.", DescribeRole.Theorem),
            Node("odd_ladder_rigidity", "odd ladder rigidity", "Exact declaration: theorem odd_ladder_rigidity {n : ℕ} (hn : n%2=1) (c : Fin n → ℕ) (hcap : ∀ i, c i≤2) (hpair : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → c i+c j≤2) (htotal : n+1 ≤ ∑ i, c i) : ∀ i, c i=if i.val%2=0 then 2 else 0.", DescribeRole.Theorem)), []));
}
