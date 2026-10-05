using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FibonacciRankSizeDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common index splits the Fibonacci Euler ratio into small ranks and a bounded tail.",
        H("Fibonacci Rank Size Decomposition"),
        Blocks(
            Paragraph(Text("F(d) is the d-th Fibonacci number, phi is Euler's totient, "
                + "and tau(j) counts the positive divisors of j. The cutoff Y is real. "
                + "A multiplies F(d) over all positive divisors d of j with d <= Y.")),
            Describe.Lean(
                DescribeId.Create("fibonacci-common-index-rank-decomposition"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/FibonacciRankSizeDecomposition.result"),
                H("Small ranks and the remaining Euler logarithm"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural j >= 3 and real Y >= 5 with A >= 2, "
                        + "the Euler ratio of F(j) factors into the Euler ratio of A "
                        + "and the exponential of a nonnegative remainder R.")),
                    Paragraph(Text("A prime divides A exactly when it divides F(j) "
                        + "and its first positive Fibonacci zero index is at most Y. "
                        + "Thus the prime support of A gives precisely the small-rank "
                        + "Euler factors. This uses the ranks of the primes, without "
                        + "a divisibility hypothesis between A and F(j).")),
                    Paragraph(Text("The remaining primes group by their first zero "
                        + "indices d, each a divisor of j greater than Y. Each group "
                        + "has Euler logarithm at most 6*(1+log(d))/d. The decrease "
                        + "of (1+log(x))/x for x > 1 and the divisor count bound "
                        + "give the stated bound on R."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula j = F.Id("j"), d = F.Id("d"), y = F.Id("Y");
        Formula a = F.Id("A"), r = F.Id("R");
        Formula fj = new Formula.Apply(F.Id("F"), [j]);
        Formula fd = new Formula.Apply(F.Id("F"), [d]);
        Formula product = Seq(Prod, Underscore,
            Grp(Seq(d, Sp, Mid, Sp, j, Comma, Sp, d, Sp, Le, Sp, y)), Sp, fd);
        Formula bound = new Formula.Fraction(
            Seq(D(6), new Formula.Apply(Tau, [j]),
                Open, D(1), Plus, new Formula.Apply(Log, [y]), Close), y);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, j, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Sp, j, Sp, Ge, Sp, D(3), Comma, Sp, y, Sp, Ge, Sp, D(5), Comma),
            Seq(a, Sp, Eq, Sp, product, Sp, Ge, Sp, D(2), Sp, Rightarrow,
                Sp, Exists, Sp, r, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Colon),
            Seq(new Formula.Fraction(fj, new Formula.Apply(Phi, [fj])), Sp, Eq, Sp,
                new Formula.Fraction(a, new Formula.Apply(Phi, [a])),
                new Formula.Apply(Exp, [r]), Comma,
                Sp, D(0), Sp, Le, Sp, r, Sp, Le, Sp, bound)
        ]));
    }
}
