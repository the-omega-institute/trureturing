using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedHighCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closing the high cycle removes the two-hub exception", H("Closing the high cycle removes the two-hub exception"),
        Blocks(Paragraph(Text("The zero-hub score is bounded by the three cell caps. In the two-hub case the intact final high edge excludes the size-thirteen pattern. Actual graph extraction is supplied separately by ClosedCore.")),
            Node("zero_hub_score", "zero hub score", "Exact declaration: theorem zero_hub_score (first middle last : Cell) (hfirst : Valid first 0 0) (hmiddle : Valid middle 0 0) (hlast : Valid last 0 0) : 3 + first.weight + middle.weight + last.weight ≤ 12.", DescribeRole.Theorem),
            Node("closed_two_hub_score", "closed two hub score", "Exact declaration: theorem closed_two_hub_score (first middle last : Cell) (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1) (hlast : Valid last 1 1) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) (hclosedHigh : last.highRight + first.highLeft + first.highRight ≤ 2) : 3 + first.weight + middle.weight + last.weight + 2 ≤ 12.", DescribeRole.Theorem)), []));
}
