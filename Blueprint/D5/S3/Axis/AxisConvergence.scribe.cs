using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisConvergenceDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Axis/AxisConvergence.";

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula WordWeight(Formula x, Formula y, Formula n) =>
        F.Seq(F.Id("w"), F.Underscore, F.Grp(x, F.Comma, y), F.Open, n, F.Close);

    private static Formula PartialSum(Formula x, Formula y, Formula k) =>
        F.Seq(F.Id("W"), F.Underscore, F.Grp(k), F.Open, x, F.Comma, y, F.Close);

    private static Formula Abs(Formula value) => F.Seq(F.Lvert, F.Sp, value, F.Sp, F.Rvert);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ExpOf(Formula exponent) =>
        F.Seq(F.Exp, F.Open, exponent, F.Close);

    private static Formula InfiniteWordSum(Formula x, Formula y, Formula n) => F.Seq(
        F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
        F.Caret, F.Grp(F.Infty), F.Sp, WordWeight(x, y, n));

    private static Formula PositiveRealBinders(Formula x, Formula y) => F.Seq(
        F.Forall, F.Sp, x, F.Comma, y, F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
        F.D(0), F.Sp, F.Lt, F.Sp, x, F.Sp, F.Rightarrow, F.Sp);

    private static Formula SummableFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");

        return F.Disp(F.Seq(
            PositiveRealBinders(x, y),
            F.Operatorname, F.Grp(F.Id("Summable")), F.Open,
            n, F.Sp, F.Mapsto, F.Sp, WordWeight(x, y, n), F.Close, F.Dot));
    }

    private static Formula TendstoFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula k = F.Id("K");

        return F.Disp(F.Seq(
            PositiveRealBinders(x, y),
            F.Lim, F.Underscore, F.Grp(k, F.To, F.Infty), F.Sp,
            PartialSum(x, y, k), F.Sp, F.Eq, F.Sp,
            InfiniteWordSum(x, y, n), F.Dot));
    }

    private static Formula TailBoundFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula k = F.Id("K");
        Formula phi = F.Varphi;
        Formula psi = F.Psi;
        Formula budget = Fraction(Abs(psi), F.Seq(F.D(1), F.Minus, Abs(psi)));
        Formula constant = Fraction(
            ExpOf(F.Seq(Abs(y), F.Sp, F.Cdot, F.Sp, budget)),
            F.Seq(F.D(1), F.Minus, ExpOf(F.Seq(F.Minus, x))));
        Formula rate = ExpOf(F.Seq(
            F.Minus, F.Open, Fraction(x, phi), F.Close,
            F.Sp, F.Cdot, F.Sp, Power(phi, k)));

        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.Comma, y, F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, x, F.Sp, F.Rightarrow, F.Sp,
            F.Forall, F.Sp, k, F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            Abs(F.Seq(PartialSum(x, y, k), F.Sp, F.Minus, F.Sp,
                InfiniteWordSum(x, y, n))),
            F.Sp, F.Le, F.Sp, constant, F.Sp, F.Cdot, F.Sp, rate, F.Dot));
    }

    private static Formula OriginValueFormula()
    {
        Formula k = F.Id("K");

        return F.Disp(F.Seq(
            F.Forall, F.Sp, k, F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            PartialSum(F.D(0), F.D(0), k), F.Sp, F.Eq, F.Sp,
            F.Id("Fib"), F.Underscore, F.Grp(k, F.Plus, F.D(1)), F.Dot));
    }

    private static Formula OriginDivergenceFormula()
    {
        Formula k = F.Id("K");

        return F.Disp(F.Seq(
            F.Lim, F.Underscore, F.Grp(k, F.To, F.Infty), F.Sp,
            PartialSum(F.D(0), F.D(0), k), F.Sp, F.Eq, F.Sp,
            F.Plus, F.Infty, F.Dot));
    }

    private static Formula OriginPackageFormula()
    {
        Formula k = F.Id("K");

        return F.Disp(F.Seq(
            F.Open,
            F.Forall, F.Sp, k, F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            PartialSum(F.D(0), F.D(0), k), F.Sp, F.Eq, F.Sp,
            F.Id("Fib"), F.Underscore, F.Grp(k, F.Plus, F.D(1)),
            F.Close, F.Sp, F.Land, F.Sp,
            F.Open,
            F.Lim, F.Underscore, F.Grp(k, F.To, F.Infty), F.Sp,
            PartialSum(F.D(0), F.D(0), k), F.Sp, F.Eq, F.Sp,
            F.Plus, F.Infty,
            F.Close, F.Dot));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-x Zeckendorf axis sums converge, with a doubly-exponential depth tail.",
        H("Axis Convergence"),
        Blocks(
            Paragraph(Text(
                "Each natural number is read through its Zeckendorf digits. Positivity of the "
                    + "first coordinate makes the golden-ratio contribution decay at least "
                    + "geometrically in the represented integer, while the conjugate contribution "
                    + "has a uniform geometric budget. This gives absolute summability for every "
                    + "real second coordinate.")),
            Paragraph(Text(
                "The depth-K window contains exactly the integers below Fib(K+1), so ordinary "
                    + "series convergence gives convergence of the axis partial sums. The omitted "
                    + "geometric tail begins there. Comparing Fib(K+1) with phi^K / phi converts "
                    + "that tail into the displayed doubly-exponential depth bound.")),
            Paragraph(Text(
                "The condition x > 0 is essential. At x = y = 0 every word has weight one, the "
                    + "depth-K partial sum is Fib(K+1), and the sequence diverges to positive "
                    + "infinity. This is the corrected boundary clause of PZG 6.35.")),
            Describe.Lean(
                DescribeId.Create("positive-x-word-weights-are-summable"),
                DeclarationHandle.Create(LeanPrefix + "wordWeight_summable"),
                H("Positive-x word weights are summable"),
                StatementSource.FromAuthor(SummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof uses the pointwise geometric majorant obtained from the two "
                        + "Zeckendorf embedding estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-x-axis-partial-sums-converge"),
                DeclarationHandle.Create(LeanPrefix + "axisPartialSum_tendsto"),
                H("Positive-x axis partial sums converge"),
                StatementSource.FromAuthor(TendstoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Series convergence is restricted along the cofinal Fibonacci cutoffs that "
                        + "define the depth windows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-axis-tail-is-doubly-exponentially-small"),
                DeclarationHandle.Create(LeanPrefix + "axisPartialSum_tail_bound"),
                H("The axis tail is doubly exponentially small"),
                StatementSource.FromAuthor(TailBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact geometric tail constant is retained, and the Fibonacci cutoff is "
                        + "bounded below by phi^K / phi to obtain the depth rate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-origin-window-is-fibonacci"),
                DeclarationHandle.Create(LeanPrefix + "axisPartialSum_zero_zero"),
                H("The origin window is Fibonacci"),
                StatementSource.FromAuthor(OriginValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every word weight is one at the origin, so the window cardinality is exactly "
                        + "the next Fibonacci number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-origin-window-diverges"),
                DeclarationHandle.Create(LeanPrefix + "axisPartialSum_zero_zero_tendsto_atTop"),
                H("The origin window diverges"),
                StatementSource.FromAuthor(OriginDivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Fibonacci identity turns standard Fibonacci growth into divergence of "
                        + "the partial sums to positive infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-origin-counterexample-package"),
                DeclarationHandle.Create(LeanPrefix + "axisPartialSum_zero_zero_package"),
                H("The origin counterexample package"),
                StatementSource.FromAuthor(OriginPackageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This conjunction binds the exact Fibonacci value at every depth together "
                        + "with divergence to positive infinity."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Axis/AxisPartialSum")),
        ]));
}
