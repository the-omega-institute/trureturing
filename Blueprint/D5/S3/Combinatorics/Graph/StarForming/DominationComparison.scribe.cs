using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DominationComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DominationComparison.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper domination and independence in bipartite graphs", H("Upper domination and independence in bipartite graphs"),
        Blocks(Paragraph(Text("Closed-neighborhood domination and inclusion-minimality define the actual finite upper-domination maximum Gamma. The classical private-neighbor exchange sends each minimal dominating selection to an independent selection of the same cardinality, proving Gamma equals Mathlib independence number in every finite bipartite graph. Positive regularity gives twice alpha equal to the order. Empty and disconnected graphs remain included; neither SF nor psiSq is identified with Gamma.")),
            Node("Dominates", "Dominates", "Exact declaration: def Dominates (D : Finset V) : Prop.", DescribeRole.Definition),
            Node("MinimalDominating", "MinimalDominating", "Exact declaration: def MinimalDominating (D : Finset V) : Prop.", DescribeRole.Definition),
            Node("minimal_dominating_exchange", "minimal dominating exchange", "Exact declaration: theorem minimal_dominating_exchange (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (D : Finset V) (hD : MinimalDominating G D) : ∃ J : Finset V, G.IsIndepSet (J : Set V) ∧ J.card = D.card.", DescribeRole.Theorem),
            Node("gamma_eq_alpha", "gamma eq alpha", "Exact declaration: theorem gamma_eq_alpha (hG : G.Colorable 2) : Gamma G = G.indepNum.", DescribeRole.Theorem),
            Node("alpha_le_beta", "alpha le beta", "Exact declaration: theorem alpha_le_beta : G.indepNum ≤ beta G 2.", DescribeRole.Theorem),
            Node("regular_alpha_card", "regular alpha card", "Exact declaration: theorem regular_alpha_card (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : 2 * G.indepNum = Fintype.card V.", DescribeRole.Theorem)), []));
}
