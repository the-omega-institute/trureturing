using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciExternalWitnessGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual External Odd-Depth Fibonacci Witness Growth",
        H("Actual External Odd-Depth Fibonacci Witness Growth"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-external-witness-growth"),
            DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciExternalWitnessGrowth.fibonacci_external_witness_growth"),
            H("Actual External Odd-Depth Fibonacci Witness Growth"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                    Paragraph(Text("For each positive Fibonacci index n, let U(n) be the prime factors p greater than five which do not divide n and whose valuations at their first Fibonacci entry ranks are odd. Set P(n) to the maximum of five and U(n).")),
                    Paragraph(Text("For every positive n, log(n) is at most log(10) plus the Chebyshev function psi evaluated at max(5, floor((P(n)+1)/2)). The sequence P tends to infinity. For every real epsilon greater than zero, eventually (2-epsilon) log(n) is at most P(n). The lower limit of P(n)/log(n), interpreted in the extended nonnegative real numbers, is at least two.")),
                    Paragraph(Text("Eventually, if F_n is powerful, the actual prime attaining P(n) exceeds five, divides F_n, does not divide n, and has odd original depth at least three. Its square divides the Fibonacci value at its entry rank. This conditional conclusion does not assert an unbounded sequence of powerful Fibonacci values.")),
                    Paragraph(Text("The rank budget provides an explicit upper bound for indices with P(n) below any fixed threshold. This proves divergence and permits the quantitative prime number theorem to be applied along the actual rank cutoff. The fixed logarithmic term is absorbed to obtain the lower growth bound."))),
            DescribeRole.Theorem))));
}
