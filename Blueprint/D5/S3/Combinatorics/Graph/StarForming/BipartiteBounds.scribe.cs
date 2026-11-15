using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class BipartiteBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bipartition classes bound the actual maximum", H("Bipartition classes bound the actual maximum"),
        Blocks(Paragraph(Text("Each color class of an actual two-coloring is independent and therefore dissociation. The two class cardinalities add to the whole finite order, proving n<=2 beta two with no regularity, nonempty or connectedness restriction. The classes need not have equal size.")),
            Node("color_class_independent", "color class independent", "Exact declaration: theorem color_class_independent (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) (i : Fin 2) : IsKIndependent G 2 (Finset.univ.filter (fun v => c v = i)).", DescribeRole.Theorem),
            Node("card_le_two_beta", "card le two beta", "Exact declaration: theorem card_le_two_beta (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Colorable 2) : Fintype.card V ≤ 2 * beta G 2.", DescribeRole.Theorem)), []));
}
