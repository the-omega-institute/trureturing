using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-axis word sums converge with an explicit double-exponential tail, and "
            + "every finite truncation has a strictly positive remainder.",
        H("Axis Convergence"),
        Blocks(Describe.Lean(
            DescribeId.Create("axis-double-exponential-tail"),
            DeclarationHandle.Create(
                "D5/S3/Axis/AxisConvergence."
                    + "axisPartialSum_tsum_double_exponential_tail"),
            H("The axis truncation has a double-exponential tail"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For x strictly positive and arbitrary real y, each word weight is "
                        + "bounded by exp(|y| B) exp(-x)^n, where B is "
                        + "|psi|/(1 - |psi|). This proves summability by comparison with a "
                        + "geometric series.")),
                Paragraph(Text(
                    "The main-embedding estimate uses the exact Zeckendorf Fibonacci sum. "
                        + "The conjugate estimate uses distinct occupied indices and the full "
                        + "geometric series in |psi|. Summing from fib(K + 1) gives a geometric "
                        + "tail, and phi^K/phi <= fib(K + 1) converts it to the displayed "
                        + "double-exponential rate.")),
                Paragraph(Text(
                    "The companion theorem axisPartialSum_lt_tsum supplies the other side: "
                        + "every finite truncation omits a strictly positive word. Thus the "
                        + "absolute error being bounded is never vacuously zero.")),
                Paragraph(Text(
                    "The condition 0 < x is essential. At x = y = 0 every word has weight "
                        + "one and the partial sums diverge along the Fibonacci cutoffs."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Axis/AxisPartialSum")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/AnalyticClosure/PositiveSeriesTail")),
        ]));

    private static Formula Abs(Formula value) => Seq(Bar, value, Bar);

    private static Formula ExpOf(Formula value) => Seq(Exp, Grp(value));

    private static Formula WordWeight(Formula x, Formula y, Formula n) =>
        Seq(Operatorname, Grp(F.Id("wordWeight")), Open,
            x, Comma, Sp, y, Comma, Sp, n, Close);

    private static Formula AxisSum(Formula x, Formula y, Formula k) =>
        Seq(Operatorname, Grp(F.Id("axisPartialSum")), Open,
            x, Comma, Sp, y, Comma, Sp, k, Close);

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula k = F.Id("K");
        Formula n = F.Id("n");
        Formula absPsi = Abs(Psi);
        Formula budget = Seq(Frac, Grp(absPsi), Grp(D(1), Minus, absPsi));
        Formula amplitude = ExpOf(Seq(Abs(y), Cdot, budget));
        Formula denominator = Seq(D(1), Minus, ExpOf(Seq(Minus, x)));
        Formula constant = Seq(Frac, Grp(amplitude), Grp(denominator));
        Formula phiPower = Seq(Phi, Caret, Grp(k));
        Formula decay = ExpOf(Seq(
            Minus, Frac, Grp(x), Grp(Phi), Cdot, phiPower));
        Formula total = Seq(
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty), Sp,
            WordWeight(x, y, n));

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("R")), Comma, Sp,
            k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(0), Sp, Lt, Sp, x, Sp, Rightarrow, Sp,
            Abs(Seq(AxisSum(x, y, k), Sp, Minus, Sp, total)), Sp,
            Leq, Sp, constant, Cdot, decay, Dot));
    }
}
