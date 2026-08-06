using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/GoldenPartition",
            "Consecutive Fibonacci weights on inverse golden powers partition one exactly."),
        H("Golden Fibonacci Partition"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-weighted-inverse-golden-powers-partition-one"),
                H("Fibonacci-weighted inverse golden powers partition one"),
                LeanTheorem("D5/S1/Recurrence/GoldenPartition.fibonacci_golden_partition"),
                Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Varphi, Caret, Grp(Minus, F.Id("n")), Plus,
                    F.Id("F"), Underscore, Grp(F.Id("n")), Varphi, Caret, Grp(Minus, Open, F.Id("n"), Plus, D(1), Close), Eq, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural index n, F_(n+1) times phi to the power -n plus F_n times phi to the power -(n+1) equals one exactly. The proof embeds the GoldenInt Fibonacci-coordinate identity into the reals and clears a nonzero golden power.")))
            ))));
}
