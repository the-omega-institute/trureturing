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
                    "Under the balanced single-peak hypotheses with 0 < r < 1, every survival mass is "
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
        Formula numerator = Seq(D(1), Minus, p, u, Minus, p, r, u, Caret, Grp(D(2)));
        Formula denominator = Seq(
            D(1), Minus, u, Plus, p, Open, D(1), Minus, r, Close, u, Caret, Grp(D(2)),
            Plus, p, r, u, Caret, Grp(D(3)));
        return Disp(Seq(
            p, Eq, Frac, Grp(D(1)), Grp(D(2), Vert, F.Id("X"), Vert), Sp, Rightarrow, Sp,
            Forall, Sp, t, Comma, Sp, D(0), Le, Survival(t), Comma, Quad,
            Survival(Seq(t, Plus, D(1))), Le, Survival(t), Comma, Quad,
            Lim, Underscore, Grp(t, To, Infty), Sp, Survival(t), Eq, D(0), Comma, Quad,
            Sum, Underscore, Grp(t, Geq, D(0)), Sp, Survival(t), Eq,
              D(2), Vert, F.Id("X"), Vert, Minus, D(1), Minus, r, Comma, Quad,
            D(0), Le, u, Le, D(1), Sp, Rightarrow, Sp,
            Sum, Underscore, Grp(t, Geq, D(0)), Sp, Survival(t), u, Caret, Grp(t), Eq,
              Frac, Grp(numerator), Grp(denominator)));
    }
}
