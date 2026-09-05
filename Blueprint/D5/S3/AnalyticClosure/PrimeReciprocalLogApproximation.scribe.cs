using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class PrimeReciprocalLogApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime reciprocal logarithms approximate positive offsets with quadratic error.",
        H("Prime Reciprocal-Log Approximation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-reciprocal-log-quadratic-approximation"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/PrimeReciprocalLogApproximation."
                    + "prime_reciprocal_log_quadratic_approximation"),
                H("A single prime sees every positive offset"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real offset delta, set Y = exp(1/delta) and "
                            + "N = ceil(Y). Bertrand's theorem supplies a prime q between N "
                            + "and 2N, while the ceiling estimate puts 2N below 4Y.")),
                    Paragraph(Text(
                        "Monotonicity of the logarithm gives the displayed logarithmic "
                            + "window. Taking reciprocals then yields a nonnegative error "
                            + "strictly below log(4) times delta squared.")),
                    Paragraph(Text(
                        "The same witnesses bound the infimum distance to the set of prime "
                            + "reciprocal logarithms, proving the right-hand big-O statement "
                            + "at zero. No uniform nearest-prime selector is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula delta = F.Id("delta");
        Formula y = F.Id("Y");
        Formula n = F.Id("N");
        Formula q = F.Id("q");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula oneOverDelta = Seq(Frac, Grp(D(1)), Grp(delta));
        Formula logQ = Seq(Log, Open, q, Close);
        Formula oneOverLogQ = Seq(Frac, Grp(D(1)), Grp(logQ));
        Formula logFour = Seq(Log, Open, D(4), Close);
        Formula deltaSq = Seq(delta, Caret, Grp(D(2)));
        Formula pointwise = Seq(
            Forall, Sp, delta, Colon, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Rightarrow, Sp,
            Exists, Sp, y, Colon, Sp, reals, Comma, Sp,
            n, Comma, Sp, q, Colon, Sp, naturals, Comma, Sp,
            y, Sp, Eq, Sp, Exp, Open, oneOverDelta, Close, Sp, Land, Sp,
            n, Sp, Eq, Sp, Call("natCeil", y), Sp, Land, Sp,
            Call("Prime", q), Sp, Land, Sp,
            n, Sp, Lt, Sp, q, Sp, Land, Sp,
            q, Sp, Leq, Sp, D(2), Sp, Times, Sp, n, Sp, Land, Sp,
            D(2), Sp, Times, Sp, n, Sp, Leq, Sp, D(4), Sp, Times, Sp, y, Sp, Land, Sp,
            oneOverDelta, Sp, Lt, Sp, logQ, Sp, Land, Sp,
            logQ, Sp, Leq, Sp, oneOverDelta, Sp, Plus, Sp, logFour, Sp, Land, Sp,
            D(0), Sp, Leq, Sp, delta, Sp, Minus, Sp, oneOverLogQ, Sp, Land, Sp,
            delta, Sp, Minus, Sp, oneOverLogQ, Sp, Lt, Sp,
            logFour, Sp, Times, Sp, deltaSq);
        Formula spectrum = F.Id("primeReciprocalLogSpectrum");
        Formula distanceFunction = Seq(
            Open, delta, Sp, Mapsto, Sp, Call("infDist", delta, spectrum), Close);
        Formula squareFunction = Seq(Open, delta, Sp, Mapsto, Sp, deltaSq, Close);
        Formula rightZero = Call("nhdsWithin", D(0), Call("Ioi", D(0)));
        Formula bigO = Call("IsBigO", distanceFunction, rightZero, squareFunction);
        return Disp(Seq(Open, pointwise, Close, Sp, Land, Sp, Open, bigO, Close, Dot));
    }
}
