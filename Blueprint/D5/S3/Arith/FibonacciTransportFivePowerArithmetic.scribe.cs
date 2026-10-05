using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FibonacciTransportFivePowerArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The CRT period arithmetic for the 2 times 59 times 5-power family.",
        H("Fibonacci transport five-power CRT arithmetic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-transport-five-power-crt-lcm"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciTransportFivePowerArithmetic.fibonacci_transport_five_power_crt_lcm"),
                H("The common CRT period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural exponent a, the least common multiple of the "
                        + "period factors three, four times five to the a, and fifty-eight "
                        + "is three hundred forty-eight times five to the a. The calculation "
                        + "uses the coprime factorization of fifty-eight and the fact that "
                        + "five is coprime to twenty-nine."))),
                DescribeRole.Theorem)),
        []));
}
