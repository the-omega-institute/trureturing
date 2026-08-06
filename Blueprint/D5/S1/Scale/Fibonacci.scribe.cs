using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Scale/Fibonacci",
            "Golden powers have Fibonacci coordinates and yield an exact inverse-power partition."),
        H("Fibonacci Coordinates of Golden Powers"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-powers-have-fibonacci-coordinates"),
                H("Golden powers have Fibonacci coordinates"),
                LeanTheorem("D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair"),
                Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Varphi, Caret, Grp(F.Id("n"), Plus, D(1)), Eq,
                    Langle, F.Id("F"), Underscore, Grp(F.Id("n")), Comma,
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Rangle)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural index n, the integral and golden coordinates of phi to the power n + 1 are F_n and F_(n+1), respectively.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-weighted-inverse-golden-powers-partition-one"),
                H("Fibonacci-weighted inverse golden powers partition one"),
                LeanTheorem("D5/S1/Scale/Fibonacci.fibonacci_golden_partition"),
                Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Varphi, Caret, Grp(Minus, F.Id("n")), Plus,
                    F.Id("F"), Underscore, Grp(F.Id("n")), Varphi, Caret, Grp(Minus, Open, F.Id("n"), Plus, D(1), Close), Eq, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural index n, F_(n+1) times phi to the power -n plus F_n times phi to the power -(n+1) equals one exactly. The proof embeds the preceding integral coordinate identity into the reals and clears the nonzero golden power.")))
            ))));
}
