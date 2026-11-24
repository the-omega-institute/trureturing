using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class WeightedCumulativeRemainderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/WeightedCumulativeRemainder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A logarithmic cumulative error gives a weighted bound uniform in the upper height.",
        H("Weighted transfer of a cumulative error"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-tail-logarithmic-error"),
            DeclarationHandle.Create(Module + ".weighted_tail_error_le"),
            H("Error bound for a weighted finite tail"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The interval has 1 ≤ X ≤ T. The finite set S indexes complex jumps a(j) " +
                    "at heights h(j) in (X,T]. Multiple indices can have equal height. The " +
                    "cumulative value C(t) adds the jumps at heights at most t to the arbitrary " +
                    "complex baseline C₀. The complex main term G has continuous derivative g.")),
                Paragraph(Text(
                    "The real weight w has continuous derivative and satisfies 0 ≤ w(t) ≤ 1/t " +
                    "and w′(t) ≤ 0 on the interval. The error profile uses c ≥ 1 and A,B ≥ 0. " +
                    "The displayed hypothesis on the cumulative error holds for each t in [X,T].")),
                Paragraph(Text(
                    "For an individual jump, integrate the weight derivative from its height " +
                    "to T. Summing these identities gives finite partial summation. Apply " +
                    "integration by parts to the main term. For an envelope E, the two endpoint " +
                    "errors and the integrated error are bounded by 2 w(X) E(X) plus the " +
                    "integral of w E′. Integration by parts for the product w E cancels the " +
                    "right endpoint. Bound the remaining integral by replacing w with 1/t " +
                    "and evaluating the logarithmic primitive.")),
                Paragraph(Text(
                    "For Ford and Zaharescu's Lemma 1, on the Riemann hypothesis, take the " +
                    "literal ordinate phases with multiplicity and use the prime-power main " +
                    "term divided by the square root of the frequency parameter x. For an " +
                    "explicit-formula error constant K the parameters are c=2x, A=K sqrt(x), " +
                    "and B=K/(sqrt(x) log(x)). The estimate is uniform in T for fixed x. " +
                    "Control of the full frequency range for growing moments remains open. " +
                    "https://arxiv.org/pdf/math/0405459"))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var x = F.Id("X");
        var limit = F.Id("T");
        var t = F.Id("t");
        var j = F.Id("j");
        var c = F.Id("c");
        var a = F.Id("A");
        var b = F.Id("B");
        var height = Call("h", j);
        var logX = Call("log", Seq(c, x));
        var log2X = Call("log", Seq(D(2), x));
        var integral = Seq(new Formula.Subscript(Int, x), Caret, Grp(limit), Sp,
            Call("w", t), Call("g", t), Sp, F.Id("d"), t);
        return Disp(new Formula.Aligned([
            Seq(Amp, Bar, Call("C", t), Minus, Call("G", t), Bar, Sp, Le, Sp,
                a, new Formula.Power(Call("log", Seq(c, t)), D(2)), Plus,
                b, Call("log", Seq(D(2), t)), Quad, Open, t, Sp, InMacro, Sp,
                OpenBracket, x, Comma, limit, CloseBracket, Close, Comma),
            Seq(Amp, Bar, new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, F.Id("S"))),
                Sp, Call("w", height), Call("a", j), Minus, integral, Bar, Sp, Le, Sp,
                new Formula.Fraction(Seq(D(2), a, Open, new Formula.Power(logX, D(2)),
                    Plus, logX, Plus, D(1), Close, Plus, b, Open, D(2), log2X, Plus, D(1),
                    Close), x), Dot)
        ]));
    }
}
