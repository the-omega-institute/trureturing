using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FibonacciPrimeSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/FibonacciPrimeSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "If every prime factor of n is a Fibonacci number, then sigma(1,n)/n < 241/50, and Robin's "
            + "inequality holds for every such n > 5040.",
        H("Integers Supported on Fibonacci Primes"),
        Blocks(
            Paragraph(Text(
                "A prime Fibonacci number is 2, 3, 5 or F_k with k >= 7, since F_6 = 8 is not prime "
                    + "and smaller indices give 0, 1, 2, 3 and 5. The integers considered here are "
                    + "those whose prime factors all lie in this set; exponents are unrestricted.")),
            Describe.Lean(
                DescribeId.Create("prime-support-euler-ratio-bound"),
                DeclarationHandle.Create(Prefix + "ratio_le_prod"),
                H("The divisor ratio is bounded by its support Euler product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural number n != 0, sigma(1,n)/n <= prod p/(p-1) over "
                            + "the distinct prime factors of n. No Fibonacci hypothesis is needed.")),
                    Paragraph(Text(
                        "This is the existing geometric-sum saturation lemma, now exposed for "
                            + "reuse by the five-prime residual proof. The finite product of prime "
                            + "powers reconstructs n, and each normalized geometric sum is at "
                            + "most p/(p-1). The original Fibonacci proof continues to consume "
                            + "the same declaration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-support-ratio-bound"),
                DeclarationHandle.Create(Prefix + "sigma_div_lt_of_fibonacci_primeFactors"),
                H("A uniform bound for the divisor ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural number n != 0 whose prime factors are all Fibonacci "
                            + "numbers, sigma(1,n)/n < 241/50.")),
                    Paragraph(Text(
                        "The frozen geometric-sum bound gives sigma(1,n)/n <= prod p/(p-1) over the "
                            + "prime factors of n. The primes 2, 3 and 5 contribute at most "
                            + "2*(3/2)*(5/4) = 15/4. For k >= 7 the Fibonacci growth "
                            + "3*F_{k} <= 2*F_{k+1} gives 3/(F_{k+1}-1) <= 2/(F_k-1), so the "
                            + "reciprocals 1/(F_k-1) for 7 <= k < M telescope below "
                            + "3*(1/12 - 1/(F_M-1)) < 1/4. With p/(p-1) <= exp(1/(p-1)), the "
                            + "remaining primes contribute at most exp(1/4) < 1.2841, and "
                            + "15/4*1.2841 < 241/50.")),
                    Paragraph(Text(
                        "The bound does not grow with n: the Fibonacci primes are too sparse for "
                            + "their Euler product to diverge. Integers supported on them therefore "
                            + "never approach the colossally abundant numbers, whose ratio grows like "
                            + "e^gamma*log(log(n))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-support-robin"),
                DeclarationHandle.Create(Prefix + "robin_of_fibonacci_primeFactors"),
                H("Robin's inequality on Fibonacci-prime support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural number n > 5040 whose prime factors are all Fibonacci "
                            + "numbers, sigma(1,n)/n < e^gamma*log(log(n)). No Riemann Hypothesis "
                            + "premise is used.")),
                    Paragraph(Text(
                        "Below the ninth primorial 223092870 the frozen theorem for 5040 < n < "
                            + "223092870 applies. From there on n > 2^24, a rational bracket of the "
                            + "frozen dyadic logarithms gives log(log(2^24)) > 14/5, and the frozen "
                            + "lower bound e^gamma > 89/50 gives a capacity above 4.98, while the "
                            + "ratio stays below 4.82.")),
                    Paragraph(
                        Text("By Robin's criterion as recalled in "),
                        Ref("D5/L/ArithSums/choie2006robincriterion"),
                        Text(", the Riemann hypothesis is equivalent to the inequality for every "
                            + "n > 5040. This theorem covers a set of integers with bounded divisor "
                            + "ratio, where the inequality holds for an elementary reason; it gives "
                            + "no information about integers with many small prime factors, and the "
                            + "Riemann hypothesis remains open."))),
                DescribeRole.Theorem))));
}
