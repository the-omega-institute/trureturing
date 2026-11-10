using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class GridProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/GridProfile.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact path-neighborhood defect", H("Exact path-neighborhood defect"),
        Blocks(Paragraph(Text("A matching leaving an arbitrary even-indexed path vertex uncovered proves the source path-neighborhood exception. A positive defect for an independent odd-path selection forces precisely all even-indexed vertices. This reusable graph lemma supplies the expansion step of the grid row-profile proof and does not by itself assert the complete grid formula.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors {n : ℕ} (P : Finset (Fin n)) : Finset (Fin n).", DescribeRole.Definition),
            Node("card_le_neighbors_of_missing_even", "card le neighbors of missing even", "Exact declaration: theorem card_le_neighbors_of_missing_even {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (pivot : Fin n) (hp : pivot.val % 2 = 0) (hmissing : pivot ∉ P) : P.card ≤ (neighbors P).card.", DescribeRole.Theorem),
            Node("odd_path_defect_support", "odd path defect support", "Exact declaration: theorem odd_path_defect_support {n : ℕ} (hn : n % 2 = 1) (P : Finset (Fin n)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ (SimpleGraph.pathGraph n).Adj a b) (hdefect : (neighbors P).card < P.card) : ∀ i : Fin n, i ∈ P ↔ i.val % 2 = 0.", DescribeRole.Theorem)), []));
}
