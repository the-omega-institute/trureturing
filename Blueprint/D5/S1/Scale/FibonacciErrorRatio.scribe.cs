using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciErrorRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/FibonacciErrorRatio",
                "Fibonacci convergents have an exact golden residual and a limiting error ratio."),
            H("Fibonacci Convergent Error Ratio"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("exact-signed-golden-residual"),
                    DescribeKind.Theorem,
                    H("Exact signed golden residual"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio.fibonacci_golden_residual")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every natural index, multiplying the Fibonacci denominator by the "
                        + "golden ratio and subtracting the next Fibonacci number gives exactly "
                        + "the negative n-th power of the contracting factor -1/phi."))),
                    LatexStatement.Create(
                        @"$$\forall n\in\mathbb{N},\ F_n\varphi-F_{n+1}="
                        + @"-\left(-\frac{1}{\varphi}\right)^n.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("adjacent-absolute-error-ratio"),
                    DescribeKind.Theorem,
                    H("Adjacent absolute-error ratio"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Let e_n be the signed error of the shifted Fibonacci convergent "
                        + "F_(n+2)/F_(n+1). Its adjacent absolute-error ratio is exactly the "
                        + "shifted ratio F_(n+1)/F_(n+2), divided by the golden ratio."))),
                    LatexStatement.Create(
                        @"$$e_n=\varphi-\frac{F_{n+2}}{F_{n+1}},\quad "
                        + @"\frac{\lvert e_{n+1}\rvert}{\lvert e_n\rvert}="
                        + @"\frac{F_{n+1}}{F_{n+2}}\frac{1}{\varphi}.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("absolute-error-ratio-limit"),
                    DescribeKind.Theorem,
                    H("Limit of adjacent absolute-error ratios"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio."
                        + "fibonacci_convergent_error_ratio_tendsto")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The adjacent absolute-error ratios of the shifted Fibonacci "
                        + "convergents tend to the reciprocal square of the golden ratio."))),
                    LatexStatement.Create(
                        @"$$\lim_{n\to\infty}\frac{\lvert e_{n+1}\rvert}"
                        + @"{\lvert e_n\rvert}=\frac{1}{\varphi^2}.$$")))));
}
