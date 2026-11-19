using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class WeightedBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/WeightedBalance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual graph weighted balance", H("Actual graph weighted balance"),
        Blocks(Paragraph(Text("Symmetry of the actual graph interchanges the neighbor sums. Any integer weight satisfying the displayed local eigenvector identity annihilates the selected-degree balance of every actual finite set. This general summation lemma is used with the original periodic weight table, without a spectral assumption.")),
            Node("neighborSum", "neighborSum", "Exact declaration: def neighborSum (weight : V → ℤ) (v : V) : ℤ.", DescribeRole.Definition),
            Node("annihilate", "annihilate", "Exact declaration: theorem annihilate (weight : V → ℤ) (c : ℤ) (hweight : ∀ v, neighborSum G weight v + c * weight v = 0) (D : Finset V) : ∑ v : V, weight v * ((selectedDegree G D v : ℤ) + c * (if v ∈ D then 1 else 0)) = 0.", DescribeRole.Theorem)), []));
}
