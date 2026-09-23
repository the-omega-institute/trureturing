using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFMarkedStarsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFMarkedStars.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be any finite vertex type and H any finite family of subsets of V. Write N(p) for the vertices x outside p such that insert(x,p) belongs to H, K(q) for the two-element sets p with q contained in N(p), and star(c,A) for the edges {c,x} with x in A. A marked triangle packet in a disjoint-union-free family forces two exact common-link stars.",
        H("Exact stars at a marked packet"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marked-common-stars"),
                DeclarationHandle.Create(Prefix + "marked_common_stars"),
                H("The two stars and the transverse intersection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume H satisfies literal unordered-disjoint-union uniqueness: if A,B,C,D belong to H, A and B are disjoint, C and D are disjoint, and their unions agree, then either A=C and B=D or A=D and B=C. Let u,v,a,b,c be pairwise distinct. Assume K({u,v}) is exactly the family of all two-element subsets of {a,b,c}, N({u,b})={a,c}, and K({a,c})={{u,b},{v,b}}.")),
                    Paragraph(Text("Then all three equalities hold: K({a,b})=star(c,N({a,c}) intersect N({b,c})); K({b,c})=star(a,N({a,c}) intersect N({a,b})); and N({a,b}) intersect N({b,c})={u,v}. There is no restriction on the size of V, no pair-codegree bound, and no assumption that every member of H has three elements.")),
                    Paragraph(Text("The packet supplies all six triples formed by one of u,v and two of a,b,c. Thus {u,c} and {v,c} belong to K({a,b}). Disjoint-union uniqueness makes this common link intersecting. An edge avoiding c would have to contain both u and v, and hence equal {u,v}. Its extension by b would put v in N({u,b}), contradicting the mark. Every edge therefore contains c. Unfolding the exact extension relation identifies the other endpoint with N({a,c}) intersect N({b,c}), in both directions. Exchanging a and c gives the second star.")),
                    Paragraph(Text("If x belongs to both N({a,b}) and N({b,c}), the pair {b,x} belongs to K({a,c}). Its exact two-edge value forces x=u or x=v. Conversely both allowed edges extend by a and c, so u and v belong to both neighborhoods.")),
                    Paragraph(Text("The star identities identify the exact leaf supports needed in local degree comparisons. The intersection identity separates the two transverse supports after deleting u and v. These conclusions do not themselves assert a global allocation or an extremal bound for H."))),
                DescribeRole.Theorem)),
        []));
}
