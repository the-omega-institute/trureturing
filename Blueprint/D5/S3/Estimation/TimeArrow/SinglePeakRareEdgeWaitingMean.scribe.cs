using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class SinglePeakRareEdgeWaitingMeanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeWaitingMean.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rare opposite-to-peak edge has an almost surely finite waiting time with an exact mean "
            + "and rational survival generating function.",
        H("Rare-Edge Waiting Time"),
        Blocks(Describe.Lean(
            DescribeId.Create("rare-edge-waiting-mean"),
            DeclarationHandle.Create(Module + "survival_waiting_mean"),
            H("Finiteness, mean, and generating function"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assume chi takes the values 1 and -1, chi(z) = 1, |X| = 2M with M positive signs, M >= 2, "
                        + "q = r/(M-1) and 0 < r < 1. Then every survival mass is "
                        + "nonnegative, the sequence is nonincreasing, and it converges to zero. Thus the "
                        + "rare edge is reached almost surely.")),
                Paragraph(Text(
                    "The sum of the survival masses is the tail-sum identity for the waiting-time mean. "
                        + "It equals 2|X| - 1 - r.")),
                Paragraph(Text(
                    "For every u in [0,1], weighting the cubic survival recurrence by u^(T+3) and summing "
                        + "its three shifted tails gives the displayed rational generating function. "
                        + "At u = 1 it reduces to the tail-sum mean."))),
            DescribeRole.Theorem))));

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));

    private static Formula Survival(Formula horizon) => Sub(F.Id("s"), horizon);

    private static Formula MainFormula()
    {
        Formula t = F.Id("T"), u = F.Id("u"), p = F.Id("p"), r = F.Id("r");
        Formula numerator = Seq(D(1), Minus, p, Sp, u, Minus, p, Sp, r, Sp, u, Caret, Grp(D(2)));
        Formula denominator = Seq(
            D(1), Minus, u, Plus, p, Open, D(1), Minus, r, Close, Sp, u, Caret, Grp(D(2)),
            Plus, p, Sp, r, Sp, u, Caret, Grp(D(3)));
        return Disp(Seq(
            Hypotheses(), Comma, Sp, D(0), Lt, r, Lt, D(1), Comma, Sp,
            p, Eq, Frac, Grp(D(1)), Grp(D(2), Lvert, Sp, F.Id("X"), Sp, Rvert), Sp, Rightarrow, Sp,
            Forall, Sp, t, Comma, Sp, D(0), Le, Sp, Survival(t), Comma, Quad, Sp,
            Survival(Seq(t, Plus, D(1))), Le, Sp, Survival(t), Comma, Quad, Sp,
            Lim, Sp, Underscore, Grp(t, To, Sp, Infty), Sp, Survival(t), Eq, D(0), Comma, Quad, Sp,
            Sum, Underscore, Grp(t, Geq, Sp, D(0)), Sp, Survival(t), Eq,
              D(2), Lvert, Sp, F.Id("X"), Sp, Rvert, Sp, Minus, D(1), Minus, r, Comma, Quad, Sp,
            D(0), Le, Sp, u, Le, Sp, D(1), Sp, Rightarrow, Sp,
            Sum, Underscore, Grp(t, Geq, Sp, D(0)), Sp, Survival(t), Sp, u, Caret, Grp(t), Eq,
              Frac, Grp(numerator), Grp(denominator)));
    }

    private static Formula Hypotheses()
    {
        Formula x = F.Id("x"), m = F.Id("M");
        return Seq(
            Call("chi", x), Sp, InMacro, Sp, OpenBrace, Pm, Sp, D(1), CloseBrace, Comma, Sp,
            Call("chi", F.Id("z")), Eq, D(1), Comma, Sp,
            Lvert, Sp, F.Id("X"), Sp, Rvert, Eq, D(2), Sp, m, Comma, Sp,
            Lvert, Sp, OpenBrace, Call("chi", x), Eq, D(1), CloseBrace, Sp, Rvert, Eq, m, Comma, Sp,
            m, Geq, Sp, D(2), Comma, Sp,
            F.Id("q"), Eq, Frac, Grp(F.Id("r")), Grp(m, Minus, D(1)));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }
}
