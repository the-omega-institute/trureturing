using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SemanticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Semantics.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical local star semantics", H("Canonical local star semantics"),
        Blocks(Paragraph(Text("For every finite simple graph, the set-valued local predicate equals the canonical non-induced two-leaf-star predicate. Set inclusion-minimality equals canonical finset inclusion-minimality, including the empty vertex type. The graph-specific H0 maxima are stated in CompositionParameters.")),
            Node("forms_iff", "forms iff", "Exact declaration: theorem forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Forms G (↑S : Set V) ↔ IsStarForming G 2 S.", DescribeRole.Theorem),
            Node("minimal_iff", "minimal iff", "Exact declaration: theorem minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Minimal G (↑S : Set V) ↔ IsMinimalStarForming G 2 S.", DescribeRole.Theorem)), []));

}
