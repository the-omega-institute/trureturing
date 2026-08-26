using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class CompletelyRecessiveSelectionOrderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder."
            + "completely_recessive_selection_order";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completely recessive selection first appears at the ploidy order.",
        H("Completely Recessive Selection Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("completely-recessive-selection-order"),
            DeclarationHandle.Create(Declaration),
            H("The selection signal has exact ploidy order"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The all-recessive class has frequency x^p and fitness 1-s; the "
                        + "remaining class has fitness one. Mean fitness and selected allele "
                        + "mass are constructed from those two classes before normalization.")),
                Paragraph(Text(
                    "Positive selection is required for the exact-order clause: at s=0 the "
                        + "change vanishes identically. The frequency lies in [0,1], and the "
                        + "single endpoint s=x=1 is excluded because mean fitness is zero there.")),
                Paragraph(Text(
                    "The local remainder is big-O of x^(p+1). Mathlib's analytic vanishing "
                        + "order records the nonzero degree-p leading factor, and the final "
                        + "clause makes the increase with ploidy explicit."))),
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

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Multiply(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula TheoremFormula()
    {
        Formula ploidy = F.Id("p");
        Formula higherPloidy = F.Id("q");
        Formula selection = F.Id("s");
        Formula frequency = F.Id("x");
        Formula level = F.Id("k");
        Formula point = F.Id("y");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula one = D(1);
        Formula zero = D(0);

        Formula fullFrequency = Call("allRecessiveFrequency", level, point);
        Formula meanAtLevel = Call("meanFitness", level, point);
        Formula massAtLevel = Call("selectedAlleleMass", level, point);
        Formula updatedAtLevel = Call("updatedFrequency", level, point);
        Formula changeAtLevel = Call("selectionChange", level, point);
        Formula pointPower = new Formula.Power(point, Grp(level));
        Formula meanDefinition = Add(
            Multiply(Grp(Subtract(one, fullFrequency)), one),
            Multiply(fullFrequency, Grp(Subtract(one, selection))));
        Formula massDefinition = Add(
            Multiply(Grp(Subtract(point, fullFrequency)), one),
            Multiply(fullFrequency, Grp(Subtract(one, selection))));
        Formula updatedDefinition = Fraction(massAtLevel, meanAtLevel);
        Formula changeDefinition = Subtract(updatedAtLevel, point);

        Formula selectedPower = Multiply(
            selection, new Formula.Power(frequency, Grp(ploidy)));
        Formula denominator = Subtract(one, selectedPower);
        Formula meanFormula = Subtract(one, selectedPower);
        Formula updatedFormula = Fraction(
            Subtract(frequency, selectedPower), denominator);
        Formula changeFormula = Fraction(
            Seq(Minus, Grp(Multiply(
                selectedPower, Grp(Subtract(one, frequency))))),
            denominator);
        Formula changeAtP = Call("selectionChange", ploidy, frequency);
        Formula localChange = Call("selectionChange", ploidy, point);
        Formula localLeading = Seq(
            Minus, Grp(Multiply(selection, new Formula.Power(point, Grp(ploidy)))));
        Formula remainder = Subtract(localChange, localLeading);
        Formula nextPower = new Formula.Power(
            point, Grp(ploidy, Sp, Plus, Sp, one));
        Formula orderAtP = Call(
            "analyticOrderAt", Call("selectionChange", ploidy), zero);
        Formula orderAtHigher = Call(
            "analyticOrderAt", Call("selectionChange", higherPloidy), zero);

        Formula typedLevel = Seq(level, Colon, Sp, naturals);
        Formula typedPoint = Seq(point, Colon, Sp, reals);
        Formula letDefinitions = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            Call("allRecessiveFrequency", typedLevel, typedPoint),
            Sp, Colon, Eq, Sp, pointPower, Comma,
            RowBreak, Grp(),
            Call("meanFitness", typedLevel, typedPoint),
            Sp, Colon, Eq, Sp, meanDefinition, Comma,
            RowBreak, Grp(),
            Call("selectedAlleleMass", typedLevel, typedPoint),
            Sp, Colon, Eq, Sp, massDefinition, Comma,
            RowBreak, Grp(),
            Call("updatedFrequency", typedLevel, typedPoint),
            Sp, Colon, Eq, Sp, updatedDefinition, Comma,
            RowBreak, Grp(),
            Call("selectionChange", typedLevel, typedPoint),
            Sp, Colon, Eq, Sp, changeDefinition,
            Close, SemiSpace);

        return Disp(Seq(
            Forall, Sp, ploidy, InMacro, Sp, naturals, Comma, Sp,
            selection, Comma, Sp, frequency, InMacro, Sp, reals, Comma,
            RowBreak, Grp(),
            one, Sp, Leq, Sp, ploidy, Sp, Land, Sp,
            zero, Sp, Lt, Sp, selection, Sp, Land, Sp,
            selection, Sp, Leq, Sp, one, Sp, Land, Sp,
            zero, Sp, Leq, Sp, frequency, Sp, Land, Sp,
            frequency, Sp, Leq, Sp, one, Sp, Land, Sp,
            Open, selection, Sp, Lt, Sp, one, Sp, Lor, Sp,
            frequency, Sp, Lt, Sp, one, Close, Sp, Rightarrow,
            RowBreak, Grp(), letDefinitions,
            RowBreak, Grp(),
            Call("meanFitness", ploidy, frequency), Sp, Eq, Sp,
            meanFormula, Sp, Land,
            RowBreak, Grp(),
            Call("updatedFrequency", ploidy, frequency), Sp, Eq, Sp,
            updatedFormula, Sp, Land,
            RowBreak, Grp(),
            changeAtP, Sp, Eq, Sp, changeFormula, Sp, Land,
            RowBreak, Grp(),
            Call("IsBigOAtZero", point, remainder, nextPower), Sp, Land,
            RowBreak, Grp(),
            orderAtP, Sp, Eq, Sp, ploidy, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, higherPloidy, InMacro, Sp, naturals, Comma, Sp,
            ploidy, Sp, Lt, Sp, higherPloidy, Sp, Rightarrow, Sp,
            orderAtP, Sp, Lt, Sp, orderAtHigher, Dot));
    }
}
