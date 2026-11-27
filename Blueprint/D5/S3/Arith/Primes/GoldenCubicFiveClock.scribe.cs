using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicFiveClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cubic Lucas sequence has a five-adic cycle from level zero, with explicit least period at every precision.",
        H("The five-adic Lucas residue clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-five-adic-lag"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_lag"),
                H("Exact valuation at every five-adic lag"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factor of five in the native Fibonacci product contributes one digit. "
                    + "The two Fibonacci depths at five equal their index depths, whose sum "
                    + "is the depth of nine raised to the lag minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lucas-five-adic-signed-collision"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision"),
                H("Five-adic collisions are signed returns from the first level"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At precision a, two distinct levels collide exactly when their lag "
                    + "is a multiple of the signed order of three modulo 5^(a-1), "
                    + "interpreting the exponent as natural subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lucas-five-adic-explicit-collision"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision_explicit"),
                H("Explicit five-adic period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every lag is a return through precision one. At precision a greater than one, "
                    + "exactly the multiples of twice 5^(a-2) are returns, including from level zero."))),
                DescribeRole.Theorem))));
}
