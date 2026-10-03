using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenFibonacciModulusPeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Fibonacci values carry an exact fourfold return of the Fibonacci matrix.",
        H("Golden Fibonacci Modulus Period"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-multiplication-matrix"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenFibonacciModulusPeriod.goldenMatrixHom"),
                H("Multiplication in the golden residue algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the ordered basis consisting of the golden generator and one, "
                    + "the residue a+b*phi acts by the matrix with rows "
                    + "(a+b,b) and (b,a). This assignment preserves zero, one, "
                    + "addition and multiplication over any modulus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-fibonacci-modulus-matrix-period"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period"),
                H("Exact period at an odd Fibonacci modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every odd index n at least five, the Fibonacci matrix "
                    + "modulo F_n has multiplicative order exactly 4n. A matrix "
                    + "return forces F_n to divide the Fibonacci number at the "
                    + "return index. Strong divisibility and strict growth then "
                    + "force n to divide that index. At the nth power the matrix "
                    + "is scalar, and Cassini's identity makes that scalar's "
                    + "square equal to minus one. Since F_n is greater than two, "
                    + "its scalar has order four, excluding every shorter return."))),
                DescribeRole.Theorem))));
}
