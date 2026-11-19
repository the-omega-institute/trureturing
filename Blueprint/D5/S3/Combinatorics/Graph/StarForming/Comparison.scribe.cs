using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Comparison.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dissociation gives minimal star formation", H("Dissociation gives minimal star formation"),
        Blocks(Paragraph(Text("Every inclusion-maximal dissociation set is inclusion-minimal two-star-forming, without bipartiteness or degree assumptions. An uncovered outside vertex could be adjoined while preserving selected degree at most one, contradicting maximality. Removing any selected vertex fails at that vertex itself. Actual finite attainment then gives beta two at most SF two. The lower comparison is attributed to Chellali and Favaron in the received source, without a novelty claim.")),
            Node("independent_self_failure", "independent self failure", "Exact declaration: theorem independent_self_failure (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (v : V) (hv : v ∈ S) : ¬ Amplification.TwoAt G (↑(S.erase v)) v.", DescribeRole.Theorem),
            Node("independent_insert_of_failure", "independent insert of failure", "Exact declaration: theorem independent_insert_of_failure (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (x : V) (hx : x ∉ S) (hfail : ¬ Amplification.TwoAt G (↑S) x) : IsKIndependent G 2 (insert x S).", DescribeRole.Theorem),
            Node("maximal_independent_minimal", "maximal independent minimal", "Exact declaration: theorem maximal_independent_minimal (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hi : IsKIndependent G 2 S) (hmax : ∀ x, x ∉ S → ¬ IsKIndependent G 2 (insert x S)) : IsMinimalStarForming G 2 S.", DescribeRole.Theorem),
            Node("beta_le_sf", "beta le sf", "Exact declaration: theorem beta_le_sf (G : SimpleGraph V) [DecidableRel G.Adj] : beta G 2 ≤ SF G 2.", DescribeRole.Theorem)), []));
}
