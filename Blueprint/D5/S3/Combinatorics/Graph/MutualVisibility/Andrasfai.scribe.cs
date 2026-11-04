using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/Andrasfai.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic obstructions for original-host mutual visibility in the Andrasfai graphs.",
        H("Andrasfai mutual-visibility obstructions"),
        Blocks(
            Describe.Lean(DescribeId.Create("host"), DeclarationHandle.Create(Prefix + "host"),
                H("The original Cayley host"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m, the vertices are Z/(3m+2)Z. Two vertices u,v are adjacent exactly when the least nonnegative representative of v-u is congruent to 1 modulo 3. These representatives are precisely 1+3j for 0 <= j <= m; they exclude zero and are closed under negation. This is the original graph G_(m+1), with no graph G_0 introduced."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "count"),
                H("All labelled mutual-visibility subsets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cardinality of the existing Configuration type for this host. Its Visible predicate requires an existential shortest walk in the original host for every distinct selected pair and permits selected support vertices only at the endpoints. Every subset cardinality is counted, including the empty set and singletons; there is no symmetry quotient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("obstruction"), DeclarationHandle.Create(Prefix + "Obstruction"),
                H("The complete finite obstruction family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any m and subset X, an obstruction means that there are a vertex u and a natural number k with 1 <= k <= m such that u, u+(3k-1), and every u+(1+3j), 0 <= j < k, belong to X. Additions are in the same original cyclic group."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("visible-iff-no-obstruction"),
                DeclarationHandle.Create(Prefix + "visible_iff_no_obstruction"),
                H("Exact obstruction characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m and every labelled subset X, Visible(host(m),X) holds if and only if X has no obstruction. For a nonedge with displacement 3k-1 the common neighbors are exactly u+(1+3j), 0 <= j < k. Each nonedge has one of this orientation or its reverse: the nonzero displacement representatives not congruent to 1 have residues 0 or 2, interchanged by reversal. The common-neighbor calculation compares the representatives 1+3j and 3k-1, with and without modular borrowing. Every nonedge therefore has distance two. A shortest walk for such a pair has exactly one interior vertex, so visibility is equivalent to an unselected common neighbor; edges have length-one witnesses. Containment of all these common neighbors and the two endpoints is exactly failure of visibility. At m=0 the obstruction range is empty and all subsets of the two-vertex host are visible."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forbidden-factor"),
                DeclarationHandle.Create(Prefix + "ForbiddenFactor"),
                H("The regular forbidden-factor family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a vertex u and a natural k, the predicate requires k >= 1, the selected endpoints at offsets 0 and 3k-1, and all selected offsets 1+3j with 0 <= j < k. Unmentioned positions are unrestricted. Thus it is exactly the binary factor 11 (Sigma Sigma 1)^(k-1) 1 in the periodically extended membership word, including occurrences across the labelled origin."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("visible-iff-periodic-avoidance"),
                DeclarationHandle.Create(Prefix + "visible_iff_periodic_avoidance"),
                H("Unbounded periodic avoidance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m >= 1 and every subset X, original-host visibility is equivalent to absence of ForbiddenFactor(m,X,u,k) for every cyclic origin u and every natural k. Factors with k <= m are precisely the finite obstructions. A factor with k > m already selects offsets 3m+1, 0 and 1; modulo 3m+2 these form the three consecutive vertices u-1,u,u+1. They give the k=1 obstruction. This proves that the full Kleene-star family introduces no extra restriction for original graph indices at least two."))), DescribeRole.Theorem),
            Paragraph(Text("The ordinary graph-to-automaton bijection, uniqueness of closed cyclic lifts, matrix-walk count, and the full generating-series identity for count remain unproved here. In particular, periodic avoidance is not asserted for the full selected subset at m=0: the original index-one correction is necessary. No finite enumeration or fitted recurrence is a premise of these results.")))));
}
