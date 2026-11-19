using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class DisjointUnionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite disjoint unions and actual attainment", H("Finite disjoint unions and actual attainment"),
        Blocks(Paragraph(Text("For finite simple graphs and every natural k, formation and inclusion-minimality hold exactly componentwise under the graph disjoint sum. This includes empty components and k zero; in particular it proves the positive-k statement of the received source. The actual canonical maxima beta and SF are each additive. Every maximum is attained by an actual finite selection; minimal forming selections exist even in graphs without any k-star.")),
            Node("starForming_sum_left", "starForming sum left", "Exact declaration: theorem starForming_sum_left (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) : IsStarForming G k S.toLeft.", DescribeRole.Theorem),
            Node("starForming_sum_right", "starForming sum right", "Exact declaration: theorem starForming_sum_right (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) : IsStarForming H k S.toRight.", DescribeRole.Theorem),
            Node("starForming_sum_iff", "starForming sum iff", "Exact declaration: theorem starForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) : IsStarForming (G ⊕g H) k S ↔ IsStarForming G k S.toLeft ∧ IsStarForming H k S.toRight.", DescribeRole.Theorem),
            Node("minimalStarForming_sum_iff", "minimalStarForming sum iff", "Exact declaration: theorem minimalStarForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) : IsMinimalStarForming (G ⊕g H) k S ↔ IsMinimalStarForming G k S.toLeft ∧ IsMinimalStarForming H k S.toRight.", DescribeRole.Theorem),
            Node("beta_attained", "beta attained", "Exact declaration: theorem beta_attained (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ∃ S : Finset V, IsKIndependent G k S ∧ S.card = beta G k.", DescribeRole.Theorem),
            Node("minimalStarForming_exists", "minimalStarForming exists", "Exact declaration: theorem minimalStarForming_exists (G : SimpleGraph V) (k : ℕ) : ∃ S : Finset V, IsMinimalStarForming G k S.", DescribeRole.Theorem),
            Node("sf_attained", "sf attained", "Exact declaration: theorem sf_attained (G : SimpleGraph V) (k : ℕ) : ∃ S : Finset V, IsMinimalStarForming G k S ∧ S.card = SF G k.", DescribeRole.Theorem),
            Node("independent_sum_iff", "independent sum iff", "Exact declaration: theorem independent_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) (S : Finset (V ⊕ W)) : IsKIndependent (G ⊕g H) k S ↔ IsKIndependent G k S.toLeft ∧ IsKIndependent H k S.toRight.", DescribeRole.Theorem),
            Node("beta_sum", "beta sum", "Exact declaration: theorem beta_sum (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) : beta (G ⊕g H) k = beta G k + beta H k.", DescribeRole.Theorem),
            Node("sf_sum", "sf sum", "Exact declaration: theorem sf_sum (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) : SF (G ⊕g H) k = SF G k + SF H k.", DescribeRole.Theorem)), []));
}
