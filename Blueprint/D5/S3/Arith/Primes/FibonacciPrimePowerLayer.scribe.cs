using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciPrimePowerLayerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nontrivial prime-power Fibonacci quotient away from five has exact fresh entry ranks.",
        H("Complete Prime-Power Fibonacci Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-prime-power-layer"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciPrimePowerLayer.fibonacci_prime_power_layer"),
                H("Fresh ranks and original depths for every prime factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a prime different from five and let s be positive, "
                            + "excluding q = 2, s = 1. The natural quotient "
                            + "C = F_(q^s)/F_(q^(s-1)) is greater than one, is coprime "
                            + "to the denominator Fibonacci value, and is not a square. "
                            + "Every prime p dividing C has first Fibonacci entry rank q^s, "
                            + "differs from q, and has the same valuation in C as in the "
                            + "Fibonacci number at its first entry rank. At least one such "
                            + "prime has odd original depth.")),
                    Paragraph(Text(
                        "For the dyadic layers, every factor is odd because the entry rank "
                            + "of two is three. A factor with an earlier rank would divide "
                            + "both adjacent Fibonacci values. Since it is prime to their "
                            + "indices, the original-rank valuation law would give equal "
                            + "valuations in those values, contradicting its positive depth "
                            + "in the quotient. The cubic-block rank theorem handles the "
                            + "higher ternary layers, while the local entry-rank and valuation calculation "
                            + "handles primes at least seven.")),
                    Paragraph(Text(
                        "Exact rank excludes old factors and yields coprimality. "
                            + "The dyadic and cubic congruences and the odd-prime quotient "
                            + "estimates exclude squares; factorization then supplies an "
                            + "odd-depth prime. The omitted dyadic quotient equals one. "
                            + "Five is excluded because F_25/F_5 still shares a factor "
                            + "five with F_5."))),
                DescribeRole.Theorem))));
}
