using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class SpectralNoiseAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noise scales for finite power-controlled spectra", H("Noise scales for finite power-controlled spectra"), Blocks(
            Describe.Lean(DescribeId.Create("spectral-noise-asymptotics"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics"),
                H("Information growth and complete recovery"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let n be a nonnegative integer and let i range from zero through n. Choose nonnegative integer powers q(i), with q(i) at most q(n), and real functions lambda(i,T). Fix positive constants beta, c, and C. Assume that for every sufficiently small positive T and every i, c T raised to q(i) is at most lambda(i,T), and lambda(i,T) is at most C T raised to q(i). No continuity is required of these functions. In the display, powerBounds denotes these simultaneous eventual inequalities together with c and C positive and q(i) at most q(n).")),
                    Paragraph(Text("For every real alpha define I(alpha,T) as one half the sum over i of log(1+lambda(i,T)/(beta T raised to alpha)). Define R(alpha,T) as one half the sum of T raised to alpha divided by beta T raised to alpha plus lambda(i,T). For any positive variance schedule epsilon on all positive times, define R(epsilon,T) by replacing T raised to alpha in this latter expression with epsilon(T). All logarithms are natural.")),
                    Paragraph(Text("For every real alpha, including values equal to one or more occupied powers, the difference between I(alpha,T) and one half the sum of max(alpha-q(i),0) times log(1/T) is bounded as T decreases to zero. R(epsilon,T) tends to zero exactly when epsilon(T) is little-o of T raised to q(n), for every positive schedule without a continuity or power-law assumption. If alpha differs from every q(i), R(alpha,T) tends to the number of indices with q(i) greater than alpha, divided by 2 beta. Repeated powers are counted with their full multiplicity.")),
                    Paragraph(Text("Multiplying each logarithm's argument by T raised to max(alpha-q(i),0) puts it in the fixed positive interval from min(1,c/beta) to 1+C/beta. This gives a uniform bound for each logarithmic remainder. With delta(T)=epsilon(T)/T raised to q(n), all risk summands lie between zero and delta(T)/c, while the final summand is at least delta(T)/(beta delta(T)+C). Set v(T)=delta(T)/(beta delta(T)+C). The inverse relation delta=C v/(1-beta v) proves necessity of the recovery condition. The strict-threshold limit follows by separating powers above and below alpha."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alpha = Alpha, time = F.Id("T"), eps = Varepsilon;
        Formula q = F.Id("q"), i = F.Id("i"), n = F.Id("n");
        Formula qi = Call("q", i), qn = Call("q", n);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula growth = Seq(Frac, Grp(D(1)), Grp(D(2)), Sum, Underscore, Grp(i, Eq, D(0)),
            Caret, Grp(n), Sp, Call("max", Seq(alpha, Minus, qi), D(0)), Sp, Log, Open, Frac, Grp(D(1)), Grp(time), Close);
        Formula remainder = Seq(Call("I", alpha, time), Minus, growth, Eq, Call("O", D(1)));
        Formula epsTime = Seq(eps, Open, time, Close);
        Formula recovery = Seq(Lim, Underscore, Grp(time, To, D(0), Caret, Grp(Plus)), Call("R", eps, time), Eq, D(0),
            Sp, Iff, Sp, epsTime, Eq, Call("o", Seq(time, Caret, Grp(qn))));
        Formula count = Call("card", Seq(OpenBrace, i, Colon, Sp, qi, Gt, alpha, CloseBrace));
        Formula indexSet = Call("Fin", Seq(n, Plus, D(1)));
        Formula threshold = Seq(Forall, Sp, i, InMacro, indexSet, Comma, Sp, alpha, Neq, qi);
        Formula risk = Seq(Forall, Sp, alpha, InMacro, real, Comma, Sp, Open, threshold, Close, Sp, Rightarrow, Sp,
            Lim, Underscore, Grp(time, To, D(0), Caret, Grp(Plus)), Call("R", alpha, time), Eq,
            Frac, Grp(count), Grp(D(2), Sp, Beta));
        Formula positiveSchedule = Seq(Forall, Sp, time, Gt, D(0), Comma, Sp, epsTime, Gt, D(0));
        return Disp(Seq(Call("powerBounds", q, LambdaLower, F.Id("c"), F.Id("C")), Sp, Land, Sp,
            Beta, Gt, D(0), Sp, Rightarrow, Sp, Open,
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, alpha, InMacro, real, Comma, Sp, remainder,
            RowBreak, Grp(), Forall, Sp, eps, Colon, real, To, real, Comma, Sp,
            Open, positiveSchedule, Close, Sp, Rightarrow, Sp, Open, recovery, Close,
            RowBreak, Grp(), risk, End, Grp(F.Id("gathered")), Close));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
