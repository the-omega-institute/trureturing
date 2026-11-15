using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class ColoringBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree obstruction to a full injective palette", H("A degree obstruction to a full injective palette"),
        Blocks(Paragraph(Text("For every finite simple graph with a vertex of degree at least three, every admissible partial sub-quorum coloring has fewer represented colors than vertices. Equality of these cardinalities would force full support and injective coloring, contradicting the weak majority at that vertex. Actual represented colors are counted; unused labels and none are excluded.")),
            Node("palette_lt_card_of_degree", "palette lt card of degree", "Exact declaration: theorem palette_lt_card_of_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hd : 3 ≤ (Finset.univ.filter (G.Adj v)).card) (c : V → Option C) (hc : IsSubQuorum G c) : (palette c Finset.univ).card < Fintype.card V.", DescribeRole.Theorem)), []));
}
