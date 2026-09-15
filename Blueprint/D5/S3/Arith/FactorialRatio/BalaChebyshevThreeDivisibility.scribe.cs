using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaChebyshevThreeDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebyshev Factorial Ratio Divisibility by 3n+1.",
        H("Chebyshev Factorial Ratio Divisibility by 3n+1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bala-three-integrality"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FactorialRatio/"
                    + "BalaChebyshevThreeDivisibility.bala_three_integrality"),
                H("Divisibility at every natural index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural number n, including zero, the factorial ratio "
                    + "(30n)!n!/((3n+1)(15n)!(10n)!(6n)!) is an integer: "
                    + "(3n+1)(15n)!(10n)!(6n)! divides (30n)!n!. No primality or other "
                    + "additional hypothesis on n is required. Legendre's formula reduces "
                    + "the result to prime valuations. The local floor defect is nonnegative "
                    + "for every positive modulus, and it equals one when the modulus "
                    + "divides 3n+1 and is seven or at least ten. The exceptional primes two "
                    + "and five are handled by binomial valuations; three never divides 3n+1."))),
                DescribeRole.Theorem))));
}
