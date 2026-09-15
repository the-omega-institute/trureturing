using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class FibonacciFactorialBlockTailFillingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial blocks realize exact rational tail fillings with vanishing normalized capacities.",
        H("Fibonacci Factorial Block Tail Filling"),
        Blocks(
            Paragraph(Text("The Fibonacci row is divided by factorial capacities on separated finite blocks. Every nonnegative rational can be read exactly by a finite state supported after any cutoff, while the normalized capacity tends to zero and no fixed positive threshold works cofinally.")),
            Describe.Lean(
                DescribeId.Create("factorial-block-tail-filling"),
                DeclarationHandle.Create(Prefix + "factorial_block_tail_filling"),
                H("Factorial block tail filling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is a separated family whose j-th block has j times j factorial elements, each Fibonacci denominator divisible by j factorial. For every such family, factorial capacities fill all nonnegative rational tails exactly, their normalized ratios converge to zero, and the cofinal fixed-threshold divisibility condition fails."))),
                DescribeRole.Theorem))));
}
