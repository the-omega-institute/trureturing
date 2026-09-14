using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaChebyshevTwoDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven times the Chebyshev factorial ratio is divisible by 2n+1 at every natural index.",
        H("Chebyshev Factorial Ratio: The 2n+1 Clause"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bala-two-integrality"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FactorialRatio/BalaChebyshevTwoDivisibility.bala_two_integrality"),
                H("The exact multiplier seven suffices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, including zero, the positive integer "
                        + "(2n+1)(15n)!(10n)!(6n)! divides 7(30n)!n!. Equivalently, "
                        + "7A(n)/(2n+1) is integral for A(n)=(30n)!n!/((15n)!(10n)!(6n)!). "
                        + "This is Peter Bala's August 28, 2025 clause recorded in OEIS A211417; "
                        + "it is distinct from the clauses with denominators 3n+1, 5n+1 and 30n-1.")),
                    Paragraph(Text(
                        "Legendre's formula expresses each prime valuation as a sum of floor "
                        + "defects. All defects are nonnegative. Any modulus q at least nine "
                        + "that divides 2n+1 contributes one. Thus divisibility exponents from "
                        + "the second power onward always contribute. For the primes three and "
                        + "five, the largest prime power at most 30n lies above 5n and contributes "
                        + "one additional unit, strictly beyond the powers dividing 2n+1. The "
                        + "external multiplier seven supplies the possible missing first unit "
                        + "at the prime seven. All larger primes have no missing first unit."))),
                DescribeRole.Theorem))));
}
