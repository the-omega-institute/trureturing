using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class SinglePeakLogLikelihoodVarianceBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodVarianceBound."
            + "uniform_single_peak_log_likelihood_variance_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance of a uniformly started single-peak log-likelihood path is bounded by twice "
            + "its accumulated one-step information.",
        H("Uniform Single-Peak Log-Likelihood Variance Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-single-peak-log-likelihood-variance-bound"),
            DeclarationHandle.Create(Declaration),
            H("Single-peak path variance is uniformly controlled by information"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X be a finite sign space with equally many positive and negative signs, and let z "
                        + "be a distinguished positive state. For a peak strength between zero and one, the "
                        + "compensating background strength is r divided by M minus one.")),
                Paragraph(Text(
                    "The one-edge second moment psi is at most twice the mean function phi throughout the "
                        + "open unit interval. The odd correction J is nonpositive, the one-edge variance v "
                        + "is at most 2I, and I is nonnegative.")),
                Paragraph(Text(
                    "Consequently, for every nonnegative path length, both the forward path and the reversed "
                        + "path have log-likelihood variance at most 2sI. Reversing the path preserves the "
                        + "distribution of the log-likelihood sum, and the zero-length sum has zero variance."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Grp(source), Sp, To, Sp, target);
    private static Formula RealType() => Seq(Mathbb, Sp, Grp(F.Id("R")));
    private static Formula NatType() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula Mul(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Square(Formula value) => new Formula.Power(value, Grp(D(2)));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Let(Formula name, Formula value) =>
        Seq(F.Id("let"), Sp, name, Sp, Eq, Sp, value, Semi, Sp);

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X"), chi = F.Id("chi"), z = F.Id("z"), x = F.Id("x");
        Formula y = F.Id("y"), t = F.Id("t"), path = Grp(Seq(Mathbf, Sp, Grp(F.Id("x"))));
        Formula r = F.Id("r"), q = F.Id("q"), m = F.Id("M"), u = F.Id("u"), s = F.Id("s");
        Formula p = F.Id("P"), k = F.Id("k"), information = F.Id("I");
        Formula correction = F.Id("J"), variance = F.Id("v");
        Formula pReverse = new Formula.Power(p, Minus);
        Formula reverseLog = new Formula.Power(F.Id("L"), Minus);
        Formula reverseLogAt = new Formula.Apply(reverseLog, [s]);
        Formula positiveSet = Seq(
            OpenBrace, x, Sp, InMacro, Sp, carrier, Sp, Mid, Sp,
            Call("chi", x), Sp, Eq, Sp, D(1), CloseBrace);
        Formula logSum = Call("logLikelihoodSum", chi, z, r, q, s);
        Formula reversedPath = Seq(t, Sp, Mapsto, Sp,
            new Formula.Subscript(path, Seq(s, Sp, Minus, Sp, t)));

        return Disp(Seq(
            Begin, Sp, Grp(F.Id("aligned")),
            Amp, Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp,
            Call("Fintype", carrier), Comma, Sp,
            Typed(chi, Arrow(carrier, RealType())), Comma, Sp, Typed(z, carrier), Comma, Sp,
            r, Comma, Sp, q, Sp, InMacro, Sp, RealType(), Comma, Sp,
            m, Sp, InMacro, Sp, NatType(), Comma, RowBreak, Sp,
            Amp, Open, Forall, Sp, x, Sp, InMacro, Sp, carrier, Comma, Sp,
            Call("chi", x), Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            Call("chi", x), Sp, Eq, Sp, Minus, D(1), Close, Sp, Land, Sp,
            Call("chi", z), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Land, Sp, r, Sp, Lt, Sp, D(1), Comma, RowBreak, Sp,
            Amp, Card(carrier), Sp, Eq, Sp, Mul(D(2), m), Sp, Land, Sp,
            Card(positiveSet), Sp, Eq, Sp, m, Sp, Land, Sp,
            D(2), Sp, Leq, Sp, m, Sp, Land, Sp,
            q, Sp, Eq, Sp, Fr(r, Seq(m, Sp, Minus, Sp, D(1))), Sp,
            Rightarrow, Sp, RowBreak, Sp,
            Amp, Let(p, Call("kernel", chi, z, r, q, Card(carrier))),
            Let(k, Seq(m, Sp, Minus, Sp, D(1))), RowBreak, Sp,
            Amp, Let(information,
                Fr(Seq(Call("phi", r), Sp, Plus, Sp, Mul(k, Call("phi", q))), Card(carrier))),
            Let(correction,
                Fr(Seq(Call("xi", r), Sp, Minus, Sp, Mul(k, Call("xi", q))), Card(carrier))),
            RowBreak, Sp,
            Amp, Let(variance,
                Seq(Fr(Seq(Call("psi", r), Sp, Plus, Sp, Mul(k, Call("psi", q))), Card(carrier)),
                    Sp, Minus, Sp, Square(information))), RowBreak, Sp,
            Amp, Let(pReverse, Seq(Open, x, Comma, Sp, y, Close, Sp, Mapsto, Sp,
                Call("P", y, x))), RowBreak, Sp,
            Amp, Let(reverseLog, Seq(Open, s, Comma, Sp, path, Close, Sp, Mapsto, Sp,
                Call("logLikelihoodSum", chi, z, r, q, s, reversedPath))), RowBreak, Sp,
            Amp, Open, Forall, Sp, u, Sp, InMacro, Sp, RealType(), Comma, Sp,
            Abs(u), Sp, Lt, Sp, D(1), Sp, Rightarrow, Sp,
            Call("psi", u), Sp, Leq, Sp, Mul(D(2), Call("phi", u)), Close, Sp, Land, Sp,
            correction, Sp, Leq, Sp, D(0), Sp, Land, Sp,
            variance, Sp, Leq, Sp, Mul(D(2), information), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, information, Sp, Land, Sp, RowBreak, Sp,
            Amp, Forall, Sp, s, Sp, InMacro, Sp, NatType(), Comma, Sp,
            Call("pathVariance", p, s, logSum), Sp, Leq, Sp,
            Mul(Mul(D(2), s), information), Sp, Land, Sp, RowBreak, Sp,
            Amp, Forall, Sp, s, Sp, InMacro, Sp, NatType(), Comma, Sp,
            Call("pathVariance", pReverse, s, reverseLogAt), Sp, Leq, Sp,
            Mul(Mul(D(2), s), information),
            End, Sp, Grp(F.Id("aligned"))));
    }
}
