using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciPrimePowerMod31NonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fibonacci period modulo thirty-one excludes square quotients in two further prime classes.",
        H("Prime-Power Fibonacci Quotients in Two Further Residue Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-prime-power-mod31-nonsquare"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare"),
                H("Alternating nonsquare residues of prime-power quotients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a prime at least seven with residue 49 or 71 modulo 120. "
                            + "For every nonnegative k, the quotient of F_(q^(k+1)) "
                            + "by F_(q^k) is a positive integer. Its residue modulo 31 "
                            + "is 27 when k is even and 23 when k is odd, so it is not "
                            + "a square.")),
                    Paragraph(Text(
                        "The Fibonacci pair has period 30 modulo 31. In the stated "
                            + "classes, q has order two modulo 30, so the Fibonacci "
                            + "values at successive powers of q alternate between "
                            + "1 and 27 modulo 31. Fibonacci divisibility then gives "
                            + "the quotient residues; neither 27 nor 23 is a square "
                            + "modulo 31.")),
                    Paragraph(Text(
                        "The classes 1 and 119 modulo 120 and the unrestricted "
                            + "prime-power square-class statement remain outside "
                            + "this theorem."))),
                DescribeRole.Theorem))));
}
