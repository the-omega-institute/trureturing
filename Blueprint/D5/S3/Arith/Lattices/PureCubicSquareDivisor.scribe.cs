using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PureCubicSquareDivisorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime square in a cubic radicand gives an integral element outside the displayed order.",
        H("Square Divisors in a Pure Cubic Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-cubic-square-divisor"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/PureCubicSquareDivisor.square_divisor_obstructs_maximality"),
                H("An explicit element of the normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K have a rational power basis (1, theta, theta squared) of "
                            + "dimension three, with theta cubed equal to 1 + 9a for an "
                            + "integer a. The integer span of 1, theta, and "
                            + "beta = (1 + theta + theta squared)/3 is an integral subring.")),
                    Paragraph(Text(
                        "Suppose that the square of a prime p other than three divides "
                            + "1 + 9a. Then theta squared divided by p is integral: its "
                            + "cube is an integer. It cannot lie in the displayed subring. "
                            + "Indeed, comparison of theta-squared coefficients in the "
                            + "rational power basis would force p to divide three.")),
                    Paragraph(Text(
                        "Thus the displayed subring is strictly smaller than the full "
                            + "ring of integers whenever such a square divisor occurs. "
                            + "The argument supplies an obstruction to maximality; it "
                            + "does not assert maximality when no such divisor occurs."))),
                DescribeRole.Theorem))));
}
