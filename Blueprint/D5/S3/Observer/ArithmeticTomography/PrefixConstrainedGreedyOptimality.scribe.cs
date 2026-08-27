using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class PrefixConstrainedGreedyOptimalityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Antitone gains on finite depth chains admit a prefix-closed maximizer under a unit-cost budget.",
        H("Prefix-Constrained Greedy Optimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("prefix-constrained-greedy-optimality"),
            DeclarationHandle.Create(
                "D5/S3/Observer/ArithmeticTomography/PrefixConstrainedGreedyOptimality."
                    + "prefix_constrained_greedy_optimality"),
            H("Top-gain cells can be repaired to a prefix optimum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The channel type is finite and the available levels form Fin(d), so the "
                        + "candidate cell region is finite. Selecting B cells is exactly the "
                        + "budget constraint when every cell has unit cost.")),
                Paragraph(Text(
                    "Gain is publicly antitone along each channel. The selected set Top also "
                        + "satisfies the top-budget premise: every selected cell has gain at "
                        + "least that of every omitted cell.")),
                Paragraph(Text(
                    "Replacing a selected level whose predecessor is missing strictly lowers "
                        + "the sum of selected depth indices and cannot lower total gain. The "
                        + "process therefore terminates at a prefix-closed selection. Pairing "
                        + "the cells outside Top with the cells omitted from Top proves global "
                        + "optimality among all B-cell selections."))),
            DescribeRole.Theorem))));

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

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula channelType = F.Id("P");
        Formula depth = F.Id("d");
        Formula budget = F.Id("B");
        Formula gain = F.Id("g");
        Formula top = F.Id("Top");
        Formula adjusted = F.Id("A");
        Formula competitor = F.Id("C");
        Formula channel = F.Id("p");
        Formula level = F.Id("j");
        Formula earlier = F.Id("i");
        Formula inside = F.Id("a");
        Formula outside = F.Id("b");
        Formula cell = F.Id("c");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula typeUniverse = Seq(Operatorname, Grp(F.Id("Type")));
        Formula levels = Call("Fin", depth);
        Formula cellType = Seq(channelType, Sp, Times, Sp, levels);
        Formula selections = Call("Finset", cellType);
        Formula gainType = Seq(
            channelType, Sp, To, Sp, levels, Sp, To, Sp, reals);
        Formula Pair(Formula first, Formula second) =>
            Seq(Open, first, Comma, Sp, second, Close);
        Formula GainAt(Formula pair) => Apply(gain, Call("fst", pair), Call("snd", pair));
        Formula GainAtLevel(Formula p, Formula j) => Apply(gain, p, j);
        Formula Card(Formula selection) => Seq(Vert, Sp, selection, Sp, Vert);
        Formula Total(Formula selection) => Seq(
            Sum, Underscore, Grp(cell, InMacro, Sp, selection), Sp, GainAt(cell));
        Formula antitone = Seq(
            Forall, Sp, channel, Colon, Sp, channelType, Comma, Sp,
            Forall, Sp, earlier, Comma, Sp, level, Sp, InMacro, Sp, levels,
            Comma, Sp, earlier, Leq, Sp, level, Sp, Rightarrow, Sp,
            GainAtLevel(channel, level), Leq, Sp, GainAtLevel(channel, earlier));
        Formula dominates = Seq(
            Forall, Sp, inside, Sp, InMacro, Sp, top, Comma, Sp,
            Forall, Sp, outside, Colon, Sp, cellType, Comma, Sp,
            Neg, Open, outside, Sp, InMacro, Sp, top, Close, Sp, Rightarrow, Sp,
            GainAt(outside), Leq, Sp, GainAt(inside));
        Formula prefixClosed = Seq(
            Forall, Sp, channel, Colon, Sp, channelType, Comma, Sp,
            Forall, Sp, level, Sp, InMacro, Sp, levels, Comma, Sp,
            Pair(channel, level), InMacro, Sp, adjusted, Sp, Rightarrow, Sp,
            Forall, Sp, earlier, Sp, InMacro, Sp, levels, Comma, Sp,
            earlier, Lt, Sp, level, Sp, Rightarrow, Sp,
            Pair(channel, earlier), InMacro, Sp, adjusted);
        Formula competitorOptimality = Seq(
            Forall, Sp, competitor, Colon, Sp, selections, Comma, Sp,
            Card(competitor), Eq, Sp, budget, Sp, Rightarrow, Sp,
            Total(competitor), Leq, Sp, Total(adjusted));
        Formula conclusion = Seq(
            Exists, Sp, adjusted, Colon, Sp, selections, Comma, RowBreak, Grp(),
            Card(adjusted), Eq, Sp, budget, Sp, Land, Sp,
            Open, prefixClosed, Close, Sp, Land, RowBreak, Grp(),
            Total(top), Leq, Sp, Total(adjusted), Sp, Land, RowBreak, Grp(),
            Open, competitorOptimality, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, channelType, Colon, Sp, typeUniverse, Comma, Sp,
            Call("Finite", channelType), Comma, RowBreak, Grp(),
            depth, Comma, Sp, budget, Sp, InMacro, Sp, naturals, Comma, Sp,
            gain, Colon, Sp, gainType, Comma, RowBreak, Grp(),
            top, Colon, Sp, selections, Comma, RowBreak, Grp(),
            Open, antitone, Close, Sp, Land, Sp,
            Card(top), Eq, Sp, budget, Sp, Land, RowBreak, Grp(),
            Open, dominates, Close, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
