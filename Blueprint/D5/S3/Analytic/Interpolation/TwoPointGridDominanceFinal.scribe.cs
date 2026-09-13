using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class TwoPointGridDominanceFinalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-coordinate logarithmic price bound is attained at the distance envelope exactly on the upper-budget diagonal.",
        H("Two-point grid dominance and equality"),
        Blocks(
            Paragraph(Text(
                "Write logValue(x)=log(1-exp(-x)) and psiTwo(m,V)=logValue(m-sqrt(V/2))+logValue(m+sqrt(V/2)). The function gridDistance(a,b,c,d) is the minimum of the distances from c and d to [a,b]. For c,d on Fin 2, varianceFloor(c,d,A,B) is the sum of the two squared grid distances to [A/2,B/2], and corners(c,d,A,B) consists of actual endpoint pairs with sums in [A,B]. The value gridDual(c,d,M) is the infimum over nonnegative prices p of pM plus the sum, over the two coordinates, of max(logValue(c(i))-p*c(i),logValue(d(i))-p*d(i)).")),
            Describe.Lean(
                DescribeId.Create("two-point-final-psitwo-strictmono-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.psiTwo_strictMono_mean"),
                H("Strict increase in the mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real m, n and V, assume m<n and sqrt(V/2)<m. Then psiTwo(m,V)<psiTwo(n,V). Both positive evaluation points increase strictly, and logValue is strictly increasing. No nonnegativity premise on V is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-pair-value-spread-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.pair_value_spread_strict"),
                H("Strict decrease with the spread"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real m, r and R with 0<=r<R<m, logValue(m-R)+logValue(m+R)<logValue(m-r)+logValue(m+r). The complementary positive coefficients (R+r)/(2R) and (R-r)/(2R) express each inner point as a strict convex combination of the outer points. Adding the two strict concavity inequalities gives the comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-fractional-row-bound-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.fractional_row_bound_strict"),
                H("A genuine fractional row has a strict gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d,t,u,A,B and theta be real numbers. Assume c>0, c<d, t>0, A<B, at least two distinct actual pairs in {c,d} times {t,u} have sums in [A,B], 0<theta<1, and (1-theta)c+theta d+t=B. Then (1-theta)logValue(c)+theta logValue(d)+logValue(t)<psiTwo(B/2,V), where V is gridDistance(A/2,B/2,c,d) squared plus gridDistance(A/2,B/2,t,u) squared. No positivity or order restriction is imposed on u. Write m=B/2, z=(1-theta)c+theta d, s=z-m, v=gridDistance(A/2,m,c,d), and e=gridDistance(A/2,m,t,u). If V<=2s squared, strict concavity in the fractional row gives the strict gap. Otherwise e<=abs(s)<v, the actual corners locate the inner secant with endpoints m-2v-s and m+v, and sqrt(V/2)<v gives the final strict spread comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-pair-bound-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.pair_bound_strict"),
                H("A pair with a strictly smaller variance parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive x and y and real V with 0<=V<(x-y) squared divided by two, logValue(x)+logValue(y)<psiTwo((x+y)/2,V). The original pair has radius abs((x-y)/2), which is positive and strictly larger than sqrt(V/2). Its lower coordinate is positive, so the strict spread comparison applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-griddistance-lt-upper"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.gridDistance_lt_upper"),
                H("Strict improvement over the upper endpoint distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real a,m,c,d,x with x equal to c or d, a<m and x<m, gridDistance(a,m,c,d)<m-x. The point max(a,x) belongs to [a,m] and is strictly below m. Comparing the distance with this point proves the inequality. No order condition on c and d is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-actual-pair-bound-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.actual_pair_bound_strict"),
                H("A non-diagonal actual pair has a strict gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d,t,u,x,y,A,B be real numbers. Assume x is c or d, y is t or u, x>0, y>0, A<B, A<=x+y<=B, and the pair (x,y) is different from (B/2,B/2). Then logValue(x)+logValue(y)<psiTwo(B/2,V), with V the two squared grid distances for [A/2,B/2]. If the actual mean is below B/2, strict increase of psiTwo in the mean applies. If the budget is attained, one coordinate is strictly below B/2 and its distance to the interval is strictly smaller than its deviation from B/2. The total distance variance is therefore strictly smaller than the actual pair variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-grid-dual-le-greedy-pair"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.grid_dual_le_greedy_pair"),
                H("A decreasing-density fill bounds the dual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c and d be real functions on Fin 2 and M a real budget, with every c(i)>0, c(i)<d(i), and c(0)+c(1)<=M. Suppose the density (logValue(d(1))-logValue(c(1)))/(d(1)-c(1)) is at most the corresponding density for index zero. Then gridDual(c,d,M) is at most logValue(c(0))+logValue(c(1)) plus the return of greedyFill with weights d(i)-c(i), gains logValue(d(i))-logValue(c(i)), list [0,1], and budget M-c(0)-c(1). An attaining greedy list is either [0,1] or [1,0]; the two-item exchange inequality compares the latter with the chosen order. Equal densities and zero remaining budget are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-corners-swap-nontrivial"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.corners_swap_nontrivial"),
                H("Exchanging the actual-corner coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real functions c,d on Fin 2 and real A,B, nontriviality of corners(c,d,A,B) implies nontriviality of corners((c(1),c(0)),(d(1),d(0)),A,B). Swap each actual pair. Coordinate sums are preserved and distinct pairs remain distinct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-grid-dual-swap"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.grid_dual_swap"),
                H("The dual is invariant under exchanging coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real functions c,d on Fin 2 and real M, gridDual((c(1),c(0)),(d(1),d(0)),M)=gridDual(c,d,M). At every nonnegative price the two summands are exchanged, leaving the price infimum unchanged. No positivity or endpoint-order assumptions are needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-two-point-grid-dominance"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.two_point_grid_dominance"),
                H("Dominance for every positive two-point grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d be real functions on Fin 2, with 0<c(i)<d(i) for each index. Let A<B be real numbers and assume corners(c,d,A,B) contains two distinct actual pairs. Then gridDual(c,d,B)<=psiTwo(B/2,varianceFloor(c,d,A,B)). The lower sum c(0)+c(1) is at most B. Order the gains by density, apply the two-item exchange inequality to an attaining greedy list, and use the ordered-fill bound. If index one has the larger density, exchange the coordinate labels. There is no additional assumption A>0, no requirement that the two actual sums differ, and no assumption that the entire upper corner is within budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-closed-row-bound-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.closed_row_bound_strict"),
                H("Closed row weights away from the diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d,t,u,A,B,theta be real numbers. Assume c>0, c<d, t>0, A<B, two distinct actual pairs from {c,d} times {t,u} lie in the sum slab [A,B], 0<=theta<=1, and (1-theta)c+theta d+t=B. Suppose (B/2,B/2) does not belong to {c,d} times {t,u}. Then the weighted logarithmic row value is strictly below psiTwo(B/2,V), with V the sum of the squared distances from [A/2,B/2] to the two endpoint sets. At theta=0 or theta=1 use the strict actual-pair bound; for an interior weight use the strict fractional-row bound. No positivity or order premise on u is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-ordered-fill-bound-strict"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.ordered_fill_bound_strict"),
                H("Strictness for an ordered two-item fill"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d,t,u,A,B be real numbers with c>0, c<d, t>0, t<u, A<B and c+t<=B. Assume two distinct actual pairs in {c,d} times {t,u} have sums in [A,B], and (B/2,B/2) is absent from that product. Use weights (d-c,u-t), gains (logValue(d)-logValue(c),logValue(u)-logValue(t)), order [0,1] and remaining budget B-c-t. The base value logValue(c)+logValue(t) plus the greedy return is strictly smaller than psiTwo(B/2,V), where V is the two squared grid distances. The objective closed form separates a full upper corner from the two possible partial rows. The order need not be sorted by density."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-two-point-grid-strict-of-no-diagonal"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.two_point_grid_strict_of_no_diagonal"),
                H("Strict dominance when the diagonal is absent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d be real functions on Fin 2 with 0<c(i)<d(i), let A<B be real numbers, and assume corners(c,d,A,B) contains two distinct actual pairs. If B/2 is absent from at least one of {c(0),d(0)} and {c(1),d(1)}, then gridDual(c,d,B)<psiTwo(B/2,varianceFloor(c,d,A,B)). Apply the strict ordered-fill comparison after ordering by gain density. Coordinate exchange preserves both the actual-corner condition and absence of the diagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-final-two-point-grid-equality"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/TwoPointGridDominanceFinal.two_point_grid_equality"),
                H("The exact equality criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c,d be real functions on Fin 2 with 0<c(i)<d(i), and let A<B be real numbers such that corners(c,d,A,B) contains two distinct actual pairs. Then gridDual(c,d,B)=psiTwo(B/2,varianceFloor(c,d,A,B)) if and only if (B/2,B/2) belongs to {c(0),d(0)} times {c(1),d(1)}. Absence of that diagonal gives strict dominance. When the diagonal is present, both grid distances vanish and this actual pair gives the matching lower bound 2logValue(B/2). Dominance supplies the reverse inequality."))),
                DescribeRole.Theorem))));
}
