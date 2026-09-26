using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class SinglePeakRareEdgeSurvivalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoiding paths for the single-peak parity kernel satisfy an exact cubic survival recurrence.",
        H("Rare-Edge Survival Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rare-edge-survival"),
                DeclarationHandle.Create(Module + "survival"),
                H("Avoiding-path survival mass"),
                StatementSource.FromAuthor(SurvivalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The survival mass at time T is the total uniform-start weight of explicit paths "
                        + "x_0, ..., x_T that never traverse an edge from the opposite region Z to the "
                        + "peak region H. Each path weight is the product of the single-peak "
                        + "kernel along its T transitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rare-edge-survival-recurrence"),
                DeclarationHandle.Create(Module + "survival_recurrence"),
                H("Exact survival recurrence"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the sign function takes only the values 1 and -1, the peak has sign 1, "
                            + "the state space has 2M elements with M positive signs, M is at least 2, "
                            + "and q = r/(M-1). Put N = |X|, p = 1/(2N), and epsilon = 1-r.")),
                    Paragraph(Text(
                        "The mass starts at one. One forbidden edge is possible after one step and two "
                            + "placements are possible after two steps, giving s_1 = 1-p and s_2 = 1-2p. "
                            + "For every later horizon, the killed three-region transition operator obeys "
                            + "its cubic identity, yielding the displayed recurrence.")),
                    Paragraph(Text(
                        "The bridge from state paths to the three-region recursion appends one last state "
                            + "to every path, separates the final transition, and sums its kernel weight over "
                            + "the peak, bulk, and opposite regions."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));

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

    private static Formula Survival(Formula horizon) => Sub(F.Id("s"), horizon);

    private static Formula SurvivalFormula()
    {
        Formula t = F.Id("t"), x = F.Id("x"), horizon = F.Id("T");
        Formula edge = Seq(
            Call("region", Sub(x, t)), Eq, F.Id("Z"), Comma, Sp,
            Call("region", Sub(x, Seq(t, Plus, D(1)))), Eq, F.Id("H"));
        return Disp(Seq(
            Survival(horizon), Eq, Sp,
            Sum, Underscore, Grp(x, Colon, Sp, Call("path", horizon)), Sp,
            Frac, Grp(D(1)), Grp(Vert, F.Id("X"), Vert), Sp,
            Prod, Underscore, Grp(t, Lt, horizon), Sp,
            Call("P", Sub(x, t), Sub(x, Seq(t, Plus, D(1)))), Sp,
            Mathbf, Grp(D(1)), Underscore,
            Grp(Forall, Sp, t, Lt, horizon, Comma, Sp, Neg, Sp, Open, edge, Close)));
    }

    private static Formula RecurrenceFormula()
    {
        Formula t = F.Id("T"), p = F.Id("p"), epsilon = F.Id("epsilon"), r = F.Id("r");
        return Disp(Seq(
            p, Eq, Frac, Grp(D(1)), Grp(D(2), Vert, F.Id("X"), Vert), Comma, Quad,
            epsilon, Eq, D(1), Minus, r, Sp, Rightarrow, Sp,
            Survival(D(0)), Eq, D(1), Comma, Quad,
            Survival(D(1)), Eq, D(1), Minus, p, Comma, Quad,
            Survival(D(2)), Eq, D(1), Minus, D(2), p, Comma, Quad,
            Forall, Sp, t, Geq, D(0), Comma, Sp,
            Survival(Seq(t, Plus, D(3))), Eq,
            Survival(Seq(t, Plus, D(2))), Minus,
            p, epsilon, Survival(Seq(t, Plus, D(1))), Minus,
            p, r, Survival(t)));
    }
}
