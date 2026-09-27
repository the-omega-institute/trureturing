using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ThreeColorOuterBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ThreeColorOuterBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal estimates for unrestricted ordinary populations exclude potential below two at the outer mixed counts, apart from a specified one-mixed support.",
        H("Reciprocal estimates at the outer mixed counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("low-population"),
                DeclarationHandle.Create(Prefix + "low_population"),
                H("Zero or one mixed vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let k,a,b,c,d,e,f be nonnegative integers with k at most one. The paired ordinary populations are (a,b), (c,d), and (e,f), and the mixed population k has the first color. Assume a=0 implies b at most k, b=0 implies k+a=0, c=0 implies d at most k, d=0 implies k+c=0, and e=0 if and only if f=0. Write rho(n)=1/(n+1), g(n)=1/((n+1)(n+2)), and Q(a,b)=(a/(b+1)+b/(a+1))/2. Then rho(k+a+c)+rho(b+e)+rho(d+f)+k/6+Q(a,b)+Q(c,d)+Q(e,f)-k(g(a)+g(c))/2 is at least two, unless k=1, at least one of a,c is zero, and e=f=0. There is no upper bound on any ordinary population.")),
                    Paragraph(Text("For integers a,b, the identity Q(a,b)+rho(b)-1=(a-b)(a-b+1)/(2(a+1)(b+1)) is nonnegative: the two consecutive integer factors have the same weak sign. Apply this estimate to the occupied pairs when a pair is absent. A thin side with one mixed vertex has opposite population one. Its attachment correction is controlled by g(n) at most 1/6 for n at least one. If all three pairs are occupied, combine the symmetric pair estimate with the three class-reciprocal losses. Their total still leaves a lower bound exceeding two for k at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("large-population"),
                DeclarationHandle.Create(Prefix + "large_population"),
                H("At least six mixed vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let m be a function from Fin(3) to the natural numbers and x a natural-valued three by three array with zero diagonal. If the sum M of the mixed populations is at least six, then the existing whole-sum expression quadraticLower(m,x) is at least two. No cellwise mixture of quadratic and attachment-charge expressions is used.")),
                    Paragraph(Text("Put U equal to the sum of the ordinary populations. The sum of x(i,j)x(j,i) is at most U squared divided by two, and the total incoming mixed incidence is at most 2M. Cauchy inequality, first across classes and then across nonempty ordinary cells, gives the lower bound M/6+U squared/(U squared+2U+4M)+9/(U+M+3). For M at least seven, multiplication by its positive denominator gives a sum of nonnegative polynomial terms. For M=6 this bound minus two is U(7U-24)/((U squared+2U+24)(U+9)), which is nonnegative for U at least four.")),
                    Paragraph(Text("For M=6 and U at most three, put P equal to the largest full class population m(i)+sum_j x(i,j). Each nonempty-cell denominator is at most x(i,j)(P+1); hence the ordinary contribution is at least U/(2(P+1)). Cauchy on the other two classes supplies 4/(U+8-P). After including the largest-class reciprocal, the remaining inequality is (U+2)/(2(P+1))+4/(U+8-P) at least one. Its cleared numerator is nonnegative because eight times that numerator equals (4P-3U-8) squared plus U(16-U). This includes U=0."))),
                DescribeRole.Theorem))));
}
