using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciPrimePowerModularNonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Modular Fibonacci periods exclude square quotients in twenty-eight prime residue classes.",
        H("Prime-Power Fibonacci Quotients in Twenty-Eight Residue Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-prime-power-modular-nonsquare"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare"),
                H("Nonsquare successive prime-power quotients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a prime at least seven whose residue modulo 120 is "
                            + "none of 1, 49, 71, and 119. At every nonnegative "
                            + "exponent k, the positive integer quotient of "
                            + "F_(q^(k+1)) by F_(q^k) is not a square.")),
                    Paragraph(Text(
                        "The Fibonacci recurrence gives periodic values modulo eight, "
                            + "three, and five. Prime-power indices reduce to four "
                            + "phases modulo 120. A finite residue calculation shows "
                            + "that in each allowed class and phase, the quotient "
                            + "has a nonsquare residue in at least one modulus.")),
                    Paragraph(Text(
                        "The four excluded residue classes and the general Fibonacci "
                            + "square-class rigidity remain outside this theorem."))),
                DescribeRole.Theorem))));
}
