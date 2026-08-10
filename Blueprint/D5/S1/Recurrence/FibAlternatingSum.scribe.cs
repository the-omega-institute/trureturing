using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibAlternatingSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/FibAlternatingSum",
            "The parity-descending Fibonacci sum equals the next source-indexed Fibonacci number minus one."),
        H("Alternating Fibonacci Sum"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("alternating-fibonacci-sum"),
                H("Alternating Fibonacci sum"),
                LeanTheorem(
                    "D5/S1/Recurrence/FibAlternatingSum.alternating_fibonacci_sum"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("alternatingFibSum")), Open, F.Id("k"), Close, Eq,
                    Operatorname, Grp(F.Id("srcFib")), Open,
                    F.Id("k"), Plus, D(1), Close, Minus, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Use the source convention F_0 = F_1 = 1, represented by "
                    + "srcFib(k) = fib(k+1). The function alternatingFibSum takes every other "
                    + "term descending from k: it is empty at k = 0, equals srcFib(1) at k = 1, "
                    + "and satisfies alternatingFibSum(k+2) = srcFib(k+2) + alternatingFibSum(k). "
                    + "For every natural k, this full parity-descending sum is exactly "
                    + "srcFib(k+1) - 1.")))))));
}
