using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFLinearRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFLinearRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of three-element subsets of a finite vertex type. Disjoint-union uniqueness means that two disjoint members determine their unordered pair uniquely from their union. Fix a vertex c and suppose the triples avoiding c form a linear family. The link G at c may have arbitrarily large degrees. Its edges and the linear remainder give exact counts for both pair supports of H.",
        H("A cone with a linear remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active"),
                DeclarationHandle.Create(Prefix + "active"),
                H("Nonisolated vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite simple graph G, active(G) consists of the vertices with a nonempty neighborhood. Ground vertices with no incident edge are excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-step-pairs"),
                DeclarationHandle.Create(Prefix + "twoStepPairs"),
                H("Pairs having a common neighbor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("T_G=twoStepPairs(G) is the set of unordered two-element vertex sets contained in some graph neighborhood. A pair is counted once regardless of the number of its common neighbors. Diagonal pairs are excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("graph-two-step-bound"),
                DeclarationHandle.Create(Prefix + "graph_two_step_bound"),
                H("The graph support estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite simple graph with e edges and v nonisolated vertices, 2e<=v+2card(T_G). For each vertex u, let A(u) be the union of the neighborhoods of its neighbors. Each neighbor z has degree at most card(A(u)), so averaging gives card(A(u))>=sum_z d(z)/d(u) when d(u)>0. Reversing oriented edges and using a/b+b/a>=2 shows that the sum of these averages is at least the degree sum 2e. The sum of card(A(u)) is v+2card(T_G): the diagonal occurs exactly at nonisolated vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support"),
                DeclarationHandle.Create(Prefix + "support"),
                H("Pair support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S(H)=support(H) consists of the unordered pairs p with nonempty extension set N_H(p). An extension x lies outside p and satisfies insert(x,p) in H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-support"),
                DeclarationHandle.Create(Prefix + "commonSupport"),
                H("Common-link support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("T(H)=commonSupport(H) consists of the unordered pairs q with a nonempty common link K_H(q). Its members are witnessed by pairs p for which q is contained in N_H(p)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("remainder"),
                DeclarationHandle.Create(Prefix + "remainder"),
                H("Deleting the cone vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("F=remainder(H,c) consists exactly of the members of H that avoid c. The other triples correspond bijectively to the edges of the link G at c, so card(H)=e+card(F)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("linear"),
                DeclarationHandle.Create(Prefix + "Linear"),
                H("Linearity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Linear(F) means that each two-element ground pair is contained in at most one member of F. For a triple family this is equivalent to every pair extension set having cardinality at most one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("support-compensation"),
                DeclarationHandle.Create(Prefix + "support_compensation"),
                H("Exact compensation and surplus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose every member of H has three elements, H has disjoint-union uniqueness, and F=remainder(H,c) is linear. Put m=card(H), f=card(F), e=card(E(G)), and v=card(active(G)), where G is the link at c. Then card(S(H))+card(T(H))+e=2m+v+card(T_G)+f. Moreover 4m+v+2f<=2card(S(H))+2card(T(H)), and hence 2m<=card(S(H))+card(T(H)). All displayed formulas use natural-number addition and avoid truncated subtraction.")),
                    Paragraph(Text("Let r count graph edges that also lie in S(F). Linearity gives card(S(F))=3f, and the support decomposition gives card(S(H))+r=e+v+3f. The pairs of T(H) avoiding c are exactly T_G. For a fixed x distinct from c, two different pairs in K_H({c,x}) must intersect by disjoint-union uniqueness. Their completions at x would then be two remainder triples sharing a pair, contrary to linearity. Thus the r overlap edges have distinct remainder completions, giving exactly r additional common-support pairs through c. Consequently card(T(H))=card(T_G)+r. Combining these counts with the graph support estimate proves the identity and surplus.")),
                    Paragraph(Text("The result allows empty H, an empty remainder, isolated vertices, and unbounded pair codegrees. It requires a vertex whose deletion leaves a linear remainder; it does not assert that every disjoint-union-free triple family has such a vertex."))),
                DescribeRole.Theorem)),
        []));
}
