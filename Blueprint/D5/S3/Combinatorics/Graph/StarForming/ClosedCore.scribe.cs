using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual closed-core omission accounting", H("Actual closed-core omission accounting"),
        Blocks(Paragraph(Text("The twenty-vertex graph R retains its complete high six-cycle and only the two specified outside edges. Each Valid and Across inequality is extracted from an actual three-vertex path in an arbitrary dissociation selection. Full-pair indicators implement the score-preserving singleton normalization. The original cell proof gives cardinality plus the number of wholly omitted designated pairs at most twelve, without restrictions at either interface vertex or reused neighboring credits.")),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 20).", DescribeRole.Definition),
            Node("bit", "bit", "Exact declaration: def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ.", DescribeRole.Definition),
            Node("full", "full", "Exact declaration: def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ.", DescribeRole.Definition),
            Node("cell", "cell", "Exact declaration: def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell.", DescribeRole.Definition),
            Node("omitted", "omitted", "Exact declaration: def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ.", DescribeRole.Definition),
            Node("omission_bound", "omission bound", "Exact declaration: theorem omission_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) : S.card+omitted S false≤12.", DescribeRole.Theorem)), []));
}
