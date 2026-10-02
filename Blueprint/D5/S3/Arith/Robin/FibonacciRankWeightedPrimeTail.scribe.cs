using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FibonacciRankWeightedPrimeTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted prime Fibonacci first-rank tail is summable with an explicit cutoff bound.",
        H("Fibonacci Rank Weighted Prime Tail"),
        Blocks(
            Paragraph(Text("For each prime p, z(p) is the least positive d with p "
                + "dividing F(d). The cutoff y is real. Define w(y,p) as 1/(p*z(p)) "
                + "when p is prime and p exceeds y, and zero otherwise.")),
            Describe.Lean(
                DescribeId.Create("summable-fibonacci-prime-first-rank-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/FibonacciRankWeightedPrimeTail.result"),
                H("A uniform real-cutoff tail bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sum over all natural p converges, and the "
                        + "displayed bound holds for every real y at least two. "
                        + "The first-zero buckets at ranks one through five are empty, "
                        + "empty, the singleton two, the singleton three, and the "
                        + "singleton five, respectively.")),
                    Paragraph(Text("On a twofold interval with lower endpoint Y, "
                        + "split the primes according to whether z(p) is at most "
                        + "the square root of Y. For small ranks, a rank-d bucket "
                        + "has fewer than d primes, so each rank contributes at most "
                        + "1/Y. There are at most the square root of Y such ranks. "
                        + "For large ranks, each term is at most 1/(Y*sqrt(Y)), "
                        + "and the interval has at most 2Y natural numbers. "
                        + "The total is at most 3/sqrt(Y).")),
                    Paragraph(Text("Partitioning every finite prime sum into twofold "
                        + "intervals bounds it by a geometric series with ratio "
                        + "1/sqrt(2). Its ratio is at most three quarters, giving "
                        + "a uniform bound of 12/sqrt(y), hence the displayed 16/sqrt(y). "
                        + "Nonnegative finite sums with this common bound establish "
                        + "summability and the infinite-sum inequality together.")),
                    Paragraph(Text("The decay order y to the power minus one half "
                        + "is known from the twofold-interval argument in the proof "
                        + "of Theorem 1.2 in Alba Gonzalez, Luca, Pomerance and "
                        + "Shparlinski, On numbers n dividing the nth term of a "
                        + "linear recurrence, Proceedings of the Edinburgh Mathematical "
                        + "Society 55 (2012), 271-289. The explicit constant for all "
                        + "real y at least two is the FIB volume's deduction. "
                        + "No novelty claim is made."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula w = new Formula.Apply(F.Id("w"), [y, p]);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(p, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")))), Sp, w);
        Formula summable = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Summable"))),
            [Seq(F.Id("w"), Open, y, Comma, Cdot, Close)]);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Sp, y, Sp, Ge, Sp, D(2), Sp, Rightarrow),
            Seq(summable, Sp, Land, Sp, sum, Sp, Le, Sp,
                new Formula.Fraction(D(1, 6), Seq(Sqrt, Grp(y))))
        ]));
    }
}
