using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenFibDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/GoldenFibDivisibility",
                "Fibonacci divisibility detects divisibility of indices from index three onward."),
            H("Fibonacci Divisibility and Indices"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("fibonacci-divisibility-detects-index-divisibility"),
                    DescribeKind.Theorem,
                    H("Fibonacci divisibility detects index divisibility"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For natural indices a and b with a at least three, the Fibonacci "
                        + "number F_a divides F_b exactly when a divides b. The lower bound "
                        + "removes the exceptional index two, where F_2 equals one."))),
                    LatexStatement.Create(
                        @"$$a \ge 3 \implies \left(F_a \mid F_b \iff a \mid b\right)$$")))));
}
