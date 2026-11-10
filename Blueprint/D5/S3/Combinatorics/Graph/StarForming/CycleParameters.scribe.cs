using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CycleParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CycleParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact all-order cycle parameters", H("Exact all-order cycle parameters"),
        Blocks(Paragraph(Text("For every cycle of order at least three, the actual cyclic 110-word with the last vertex omitted has floor(2n/3) vertices and induced degree at most one. Its exact finite counting and the current general degree-capacity upper bound prove beta two and SF two both floor(2n/3), without a parity assumption.")),
            Node("selection", "selection", "Exact declaration: def selection (n : ℕ) : Finset (Fin n).", DescribeRole.Definition),
            Node("selection_independent", "selection independent", "Exact declaration: theorem selection_independent (n : ℕ) (hn : 3≤n) : IsKIndependent (SimpleGraph.cycleGraph n) 2 (selection n).", DescribeRole.Theorem),
            Node("selection_card", "selection card", "Exact declaration: theorem selection_card (n : ℕ) : (selection n).card=2*n/3.", DescribeRole.Theorem),
            Node("parameters", "parameters", "Exact declaration: theorem parameters (n : ℕ) (hn : 3≤n) : beta (SimpleGraph.cycleGraph n) 2=2*n/3 ∧ SF (SimpleGraph.cycleGraph n) 2=2*n/3.", DescribeRole.Theorem)), []));
}
