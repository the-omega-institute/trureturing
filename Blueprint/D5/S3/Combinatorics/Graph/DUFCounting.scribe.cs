using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of an n-element vertex type, m=card(H), and P=binom(n,2). The counts are defined for every H and include absent ground pairs; write hi=h(H,i) and qi=q(H,i). The cap means at most four neighbors per ground pair. Under the hypotheses stated below, fiber and incidence counts yield the bounds and exact correction identity.",
        H("Two incidence counts and the codegree-four bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("h"),
                DeclarationHandle.Create(Prefix + "h"),
                H("Codegree distribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("h(H,i) counts ground pairs with exactly i neighbors. In particular h0 includes absent pairs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q"),
                DeclarationHandle.Create(Prefix + "q"),
                H("Common-link size distribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("q(H,i) counts ground pairs whose common link has exactly i edges. The count includes q0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"),
                H("Small nonempty fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("a(H) counts four-element sets S for which the exact neighborhood fiber has one or two edges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("b"),
                DeclarationHandle.Create(Prefix + "b"),
                H("Four-edge fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("b(H) counts four-element sets S whose exact neighborhood fiber has four edges. Under DUF and the cap these fibers are four-edge stars."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber-counts"),
                DeclarationHandle.Create(Prefix + "fiber_counts"),
                H("The fiber correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap, q4+a=h4+2b, 4b<=h4, and 2q4<=3h4. Each fiber F(S) with card(S)=4 and k=card(F(S)) contributes binom(k,2) wedges and k codegree-four pairs; k is at most four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incidence-counts"),
                DeclarationHandle.Create(Prefix + "incidence_counts"),
                H("The two actual incidence sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a three-uniform H, the sum over ground pairs of card(N(p)) is 3m. The sum of binom(card(N(p)),2) equals the sum of card(K(q)); both sums also range over all ground pairs. The first equality counts pair-triple incidences; the second counts ordered incidences (p,q) with q contained in N(p)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counting-bound"),
                DeclarationHandle.Create(Prefix + "counting_bound"),
                H("The bound and the fiber identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a three-uniform DUF family with maximum pair codegree at most four, 21m+10h0+3h1+h3<=22P. Also 6m+a+q2+2q1+3q0+h1+3h0=6P+2b. These are additive natural-number formulas, so they remain valid when m<P without interpreting truncated subtraction as a signed difference."))),
                DescribeRole.Theorem)),
        []));
}
