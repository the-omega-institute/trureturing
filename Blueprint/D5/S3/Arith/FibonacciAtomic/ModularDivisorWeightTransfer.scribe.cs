using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ModularDivisorWeightTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial congruences control normalized divisor factors at every prime below the factorial boundary.",
        H("Local Divisor Factors on a Factorial Congruence Class"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-prime-divisor-weight"),
                DeclarationHandle.Create(Prefix + "smallWeight"),
                H("Small-prime divisor weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural m and n, smallWeight(m,n) is the product of "
                    + "reciprocalGeomSum(p,v_p(n)) over all primes p with 0 < p <= m. "
                    + "The reciprocal geometric sum ranges over i from zero through v_p(n) "
                    + "with term p^(-i); v_p(n) is the natural prime factorization exponent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-divisor-error-floor"),
                DeclarationHandle.Create(Prefix + "delta"),
                H("Factorial error floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real product delta(m) ranges over primes p with 0 < p <= m, "
                    + "with factor 1 - p^(-v_p(m!)-1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-congruence-local-divisor-stability"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Uniform local-factor squeeze and vanishing error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural m >= 2 and every pair of positive natural "
                        + "numbers a and b congruent modulo m!, the ratio "
                        + "smallWeight(m,a)/smallWeight(m,b) lies between delta(m) and "
                        + "the inverse of delta(m). For every natural m >= 4, the sum "
                        + "of p^(-v_p(m!)-1) over primes p <= m is at most "
                        + "1/sqrt(m) + 1/(sqrt(m)-1). As m tends to infinity through "
                        + "the natural numbers, delta(m)-1 is O(1/sqrt(m)).")),
                    Paragraph(Text(
                        "At each prime the congruence preserves valuations below "
                        + "v_p(m!); otherwise both valuations are at least this value. "
                        + "The geometric formula gives both ratio bounds. Powers "
                        + "of p below m divide m!, so each omitted local tail is "
                        + "at most 1/m. Split at floor(sqrt(m)): there are at most "
                        + "sqrt(m) smaller primes, while the larger tails are bounded "
                        + "by 1/(p(p-1)). Their sum telescopes after extending it to "
                        + "all integers above the cutoff. The product of 1 minus "
                        + "the tails is at least one minus their sum."))),
                DescribeRole.Theorem))));
}
