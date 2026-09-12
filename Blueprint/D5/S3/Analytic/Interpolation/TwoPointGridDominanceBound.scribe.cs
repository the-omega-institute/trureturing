using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class TwoPointGridDominanceBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic secant estimates control positive pairs, fractional rows and ordered two-item fills.",
        H("Two-point grid row bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-point-bound-psitwo-mono-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.psiTwo_mono_mean"),
                H("Increasing the mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let m, n and V be real numbers with m at most n and sqrt(V/2) strictly below m. Then psiTwo(m,V) is at most psiTwo(n,V). Here psiTwo(m,V) is the sum of logValue at m minus sqrt(V/2) and m plus sqrt(V/2), and logValue(x)=log(1-exp(-x)). Both coordinates increase with the mean and remain positive, so strict increase of logValue gives the inequality. No nonnegativity assumption on V is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-pair-value-spread"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.pair_value_spread"),
                H("Decreasing the spread"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real m, r and R with zero at most r, r at most R and R strictly below m, the sum of logValue at m-R and m+R is at most its sum at m-r and m+r. If r is smaller than R, the inner pair is obtained from the outer pair by two complementary convex combinations. Strict concavity gives a strict comparison in that case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-inner-secant-quadratic-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.inner_secant_quadratic_moments"),
                H("The quadratic moments of the inner secant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let m, v, s, A, B and C be real numbers, with v positive and the absolute value of s smaller than v. Put theta=2(v+s)/(3v+s) and P(x)=A+B(x-(m-v))+C(x-(m-v)) squared. Then (1-theta)P(m-2v-s)+theta P(m+v)+P(m-s)=P(m-v)+P(m+v). Expanding the quadratic and cancelling the nonzero denominator establishes the identity for every quadratic of this form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-inner-secant-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.inner_secant_bound"),
                H("The logarithmic inner secant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real m, v and s, assume v positive, the absolute value of s smaller than v, and m-2v-s positive. Put theta=2(v+s)/(3v+s). Then (1-theta)logValue(m-2v-s)+theta logValue(m+v)+logValue(m-s) is at most logValue(m-v)+logValue(m+v). The quadratic tangent at m-v and interpolating m+v majorizes logValue at all three positive evaluation points. The quadratic moment identity gives its sum exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-pair-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.pair_bound"),
                H("A positive pair and a variance parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive real x and y and any real V at most (x-y) squared divided by two, logValue(x)+logValue(y) is at most psiTwo((x+y)/2,V). The square root of V/2 is at most the absolute value of (x-y)/2. Apply the spread comparison after ordering the original two coordinates. The parameter V may be negative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-secant-contract"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.secant_contract"),
                H("Contracting a secant interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c, d, C, D, z and theta be real numbers. Assume c positive, c<d, c at most C, C<D, D at most d, C at most z at most D, zero at most theta at most one, and (1-theta)c+theta d=z. Then (1-theta)logValue(c)+theta logValue(d) is at most (1-(z-C)/(D-C))logValue(C)+(z-C)/(D-C)logValue(D). Concavity places the outer affine secant below logValue at C and D; interpolation at z gives the comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-fractional-row-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.fractional_row_bound"),
                H("A row meeting the upper budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c, d, t, u, A, B and theta be real numbers with c positive, c<d, t positive and A<B. Suppose the pairs in {c,d} times {t,u} whose sums lie in [A,B] contain two different elements. Assume zero<theta<one and (1-theta)c+theta d+t=B. Then (1-theta)logValue(c)+theta logValue(d)+logValue(t) is at most psiTwo(B/2,V), where V is gridDistance(A/2,B/2,c,d) squared plus gridDistance(A/2,B/2,t,u) squared. The distance is the minimum of the distances from the two endpoints to the closed interval. No ordering or positivity condition on u is assumed. If the variance parameter is small, concavity and the positive-pair bound apply. Otherwise the lower actual corner locates a contracted secant, and the inner-secant bound completes the comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-actual-pair-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.actual_pair_bound"),
                H("An actual positive pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c, d, t, u, x, y, A and B be real numbers with x equal to c or d, y equal to t or u, x and y positive, and A at most x+y at most B. Then logValue(x)+logValue(y) is at most psiTwo(B/2,V), where V is the sum of the squared distances from [A/2,B/2] to {c,d} and {t,u}. Each distance is at most its coordinate deviation from (x+y)/2. The positive-pair bound followed by increase in the mean gives the result. No strict width or ordering of the endpoint sets is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-bound-ordered-fill-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceBound.ordered_fill_bound"),
                H("An ordered two-item fill"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c, d, t, u, A and B be real numbers with c and t positive, c<d, t<u, A<B and c+t at most B. Suppose there are two different pairs in {c,d} times {t,u} whose sums lie in [A,B]. Use weights (d-c,u-t), gains (logValue(d)-logValue(c),logValue(u)-logValue(t)), the order [0,1], and remaining capacity B-c-t. The sum logValue(c)+logValue(t) plus the objective of greedyFill for these weights, order and capacity is at most psiTwo(B/2,V), where V is the sum of the two squared distances from [A/2,B/2] to the endpoint sets. The order need not be sorted by gain density. Filling both items gives an actual corner; stopping in either item gives a closed row, with endpoint cases treated as actual pairs."))),
                DescribeRole.Theorem))));
}
