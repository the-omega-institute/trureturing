using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockFibonacciLagProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A golden trace polarization factors differences of native cubic Lucas blocks into Fibonacci terms.",
        H("Fibonacci factorization of cubic Lucas block differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-lucas-signed-square-difference"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.lucas_sq_sub_signed_sq"),
                H("Signed Lucas square difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For indices n at least m, the golden norm of the intervening power "
                    + "supplies the sign on the earlier Lucas square. Golden trace "
                    + "polarization factors the result into five times the Fibonacci "
                    + "terms at the sum and difference of the indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-block-fibonacci-lag-product"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product"),
                H("Exact native cubic block lag product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The powers of three are odd, so the sign disappears for the native "
                    + "cubic blocks. The identity holds over the integers before reduction "
                    + "at any prime or precision."))),
                DescribeRole.Theorem))));
}
