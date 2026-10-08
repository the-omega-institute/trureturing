using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class WeightedInghamRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/WeightedInghamRate.";
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Fib(Formula n) => Call("F", n);
    private static Formula W(Formula n) => Call("W", n);
    private static Formula Phi(Formula x) => Call("Phi", x);
    private static Formula Constant() => new Formula.Fraction(D(2), Seq(Sqrt, Grp(D(5))));
    private static Formula Row(Formula n) => Seq(
        new Formula.Subscript(Sum, Seq(D(1), Sp, Le, Sp, F.Id("k"), Sp, Le, Sp, n)),
        Phi(new Formula.Fraction(Fib(F.Id("k")), Fib(n))));

    private static Formula WeightedSumFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(Equal(W(n), Seq(
            new Formula.Subscript(Sum, Seq(D(1), Sp, Le, Sp, k, Sp, Le, Sp, n)),
            Fib(k), Cdot, Sp, Call("fract", new Formula.Fraction(Fib(n), Fib(k))))));
    }

    private static Formula KernelFormula()
    {
        Formula x = F.Id("x");
        return Disp(Equal(Phi(x), Seq(x, Cdot, Sp,
            new Formula.Floor(new Formula.Fraction(D(1), x)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), c = F.Id("C"), n0 = F.Id("N0");
        Formula rate = Seq(c, Cdot, Sp,
            new Formula.Power(F.Id("phi"), new Formula.Fraction(Seq(Minus, n), D(2))));
        return Disp(new Formula.Aligned([
            Seq(Exists, Sp, c, Sp, Gt, Sp, D(0), Comma, Sp, Exists, Sp, n0, InMacro,
                Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, n, InMacro,
                Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, n0, Sp, Le, Sp, n, Sp, Rightarrow),
            Seq(Abs(Seq(new Formula.Fraction(W(n), Fib(n)), Minus, Constant())), Sp, Le, Sp, rate, Sp, Land),
            Seq(Abs(Seq(Row(n), Minus, Open, n, Minus, Constant(), Close)), Sp, Le, Sp, rate)
        ]));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Fibonacci fractional-part sums and their reciprocal-floor rows have a common half-exponential error bound.",
        H("A Half-Exponential Rate for Weighted Fibonacci Rows"),
        Blocks(
            Paragraph(Text("Let F be the standard Fibonacci sequence, with F(0)=0 and F(1)=1. "
                + "Let phi=(1+sqrt(5))/2. The function fract is the real fractional part "
                + "x-floor(x), and floor takes integer values.")),
            Describe.Lean(DescribeId.Create("weighted-fibonacci-sum"),
                DeclarationHandle.Create(Prefix + "weightedSum"), H("Weighted fractional-part sum"),
                StatementSource.FromAuthor(WeightedSumFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum runs over all positive indices k at most n. "
                    + "Each summand is also the integer remainder of F(n) on division by F(k). "
                    + "The empty sum at n=0 is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reciprocal-floor-kernel"),
                DeclarationHandle.Create(Prefix + "inghamKernel"), H("Reciprocal-floor kernel"),
                StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive x the kernel multiplies x by the integer part "
                    + "of its reciprocal. At x=0 real field division gives zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-half-exponential-rate"),
                DeclarationHandle.Create(Prefix + "result"), H("A common error bound"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are a positive real C and a natural threshold N0 such that "
                        + "both inequalities hold for every natural n>=N0, with the same C and N0. "
                        + "The exponent is the real number -n/2. One choice is C=4096 and N0=16.")),
                    Paragraph(Text("Put j=n-k. In the main segment 1<=j and 2j+3<=n, the integer "
                        + "Fibonacci addition identity determines the weighted fractional part exactly: "
                        + "it is F(n-j)-F(n-2j) for even j, and F(n-2j) for odd j. "
                        + "The strict inequalities 0<F(n-2j)<F(n-j) fix the integer quotient.")),
                    Paragraph(Text("Pairing j=2t+1 with j=2t+2 gives F(n-2t-2)+F(n-4t-3). "
                        + "For m=floor((n-4)/4), this finite paired sum telescopes to "
                        + "(4F(n+1)-2F(n))/5 plus boundary terms. The remaining terms are nonnegative "
                        + "and their sum is bounded by the sum of their Fibonacci weights.")),
                    Paragraph(Text("Fibonacci power bounds control all boundary terms by a constant "
                        + "times phi to the power n/2. Dividing by F(n), and using the exact golden "
                        + "residual of consecutive Fibonacci numbers, gives the first inequality. "
                        + "For each positive Fibonacci ratio, Phi(F(k)/F(n)) equals "
                        + "1-(F(k)/F(n))*fract(F(n)/F(k)); summing this equality gives the second inequality."))),
                DescribeRole.Theorem))));
}
