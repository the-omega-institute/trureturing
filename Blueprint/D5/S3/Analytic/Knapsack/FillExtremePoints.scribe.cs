using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Knapsack;

internal sealed class FillExtremePointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every extreme point of the finite fill feasible set has at most one strictly fractional coordinate.",
        H("Extreme feasible fills have at most one fractional row"),
        Blocks(
            Paragraph(Text(
                "Let I be any finite index type, let c(i) and d(i) be real endpoints with 0<c(i)<d(i), and let M be a real budget. Put w(i)=d(i)-c(i) and R=M-sum c(i). The feasible set F consists of functions a from I to the reals satisfying 0<=a(i)<=1 for every i and sum w(i)a(i)<=R.")),
            Describe.Lean(
                DescribeId.Create("extreme-fill-at-most-one-fractional"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/FillExtremePoints.extreme_fill_at_most_one_fractional"),
                H("At most one strictly fractional coordinate"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Exists, Sp,
                    F.Id("i"), Comma, Sp, F.Id("j"), Sp, InMacro, Sp, F.Id("I"), Colon, Sp,
                    F.Id("i"), Sp, Neq, Sp, F.Id("j"), Comma, Sp,
                    D(0), Sp, Lt, Sp, Call("a", F.Id("i")), Sp, Lt, Sp, D(1), Comma, Sp,
                    D(0), Sp, Lt, Sp, Call("a", F.Id("j")), Sp, Lt, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume a is an extreme point of F over the reals. Then there are no distinct indices i and j whose coordinates both lie strictly between zero and one. The assertion imposes no budget saturation or optimality hypothesis; if F is empty, it has no extreme points.")),
                    Paragraph(Text(
                        "Suppose two such indices exist. Let delta be the minimum of w(i)a(i), w(i)(1-a(i)), w(j)a(j), and w(j)(1-a(j)). All four terms are positive. Define e(i)=delta/w(i), e(j)=-delta/w(j), and e(k)=0 at every other coordinate. The four bounds on delta keep both a+e and a-e in the unit box. Their weighted sums equal that of a because sum w(k)e(k)=0, so both points are feasible.")),
                    Paragraph(Text(
                        "The point a lies in the open segment between a+e and a-e. Extremality forces a+e=a, whereas e(i)>0. This contradiction proves the claim for every finite index type, including the empty type."))),
                DescribeRole.Theorem))));
}
