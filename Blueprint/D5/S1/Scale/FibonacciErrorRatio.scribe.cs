using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciErrorRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Fibonacci convergents have an exact golden residual and a limiting error ratio.",
H("Fibonacci Convergent Error Ratio"),
Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-signed-golden-residual"),
                    DeclarationHandle.Create("D5/S1/Scale/FibonacciErrorRatio.fibonacci_golden_residual"),
                    H("Exact signed golden residual"),
                    StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("F"), Underscore, F.Id("n"), Varphi, Minus, F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Eq, Minus, Left, Open, Minus, Frac, Grp(D(1)), Grp(Varphi), Right, Close, Caret, F.Id("n"), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every natural index, multiplying the Fibonacci denominator by the "
                        + "golden ratio and subtracting the next Fibonacci number gives exactly "
                        + "the negative n-th power of the contracting factor -1/phi."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("adjacent-absolute-error-ratio"),
                    DeclarationHandle.Create("D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio"),
                    H("Adjacent absolute-error ratio"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("e"), Underscore, F.Id("n"), Eq, Varphi, Minus, Frac, Grp(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(2))), Grp(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1))), Comma, Quad, Sp, Frac, Grp(Lvert, Sp, F.Id("e"), Underscore, Grp(F.Id("n"), Plus, D(1)), Rvert), Grp(Lvert, Sp, F.Id("e"), Underscore, F.Id("n"), Rvert), Eq, Frac, Grp(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1))), Grp(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(2))), Frac, Grp(D(1)), Grp(Varphi), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Let e_n be the signed error of the shifted Fibonacci convergent "
                        + "F_(n+2)/F_(n+1). Its adjacent absolute-error ratio is exactly the "
                        + "shifted ratio F_(n+1)/F_(n+2), divided by the golden ratio."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("absolute-error-ratio-limit"),
                    DeclarationHandle.Create("D5/S1/Scale/FibonacciErrorRatio."
                        + "fibonacci_convergent_error_ratio_tendsto"),
                    H("Limit of adjacent absolute-error ratios"),
                    StatementSource.FromAuthor(Disp(Seq(Lim, Underscore, Grp(F.Id("n"), To, Infty), Frac, Grp(Lvert, Sp, F.Id("e"), Underscore, Grp(F.Id("n"), Plus, D(1)), Rvert), Grp(Lvert, Sp, F.Id("e"), Underscore, F.Id("n"), Rvert), Eq, Frac, Grp(D(1)), Grp(Varphi, Caret, D(2)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The adjacent absolute-error ratios of the shifted Fibonacci "
                        + "convergents tend to the reciprocal square of the golden ratio."))),
                    DescribeRole.Theorem))));
}
