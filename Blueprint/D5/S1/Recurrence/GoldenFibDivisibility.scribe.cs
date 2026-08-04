using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenFibDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/GoldenFibDivisibility",
            "Fibonacci divisibility detects divisibility of indices from index three onward."),
        H("Fibonacci Divisibility and Indices"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-divisibility-detects-index-divisibility"),
                H("Fibonacci divisibility detects index divisibility"),
                LeanTheorem(
                    "D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff"),
                Disp(Seq(F.Id("a"), Sp, Ge, Sp, D(3), Sp, Implies, Sp, Left, Open, F.Id("F"), Underscore, F.Id("a"), Sp, Mid, Sp, F.Id("F"), Underscore, F.Id("b"), Sp, Iff, Sp, F.Id("a"), Sp, Mid, Sp, F.Id("b"), Right, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For natural indices a and b with a at least three, the Fibonacci "
                    + "number F_a divides F_b exactly when a divides b. The lower bound "
                    + "removes the exceptional index two, where F_2 equals one.")))))));
}
