using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class DiploidDominanceSelectionOrderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder."
            + "diploid_dominance_selection_order";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diploid dominance changes the rare-allele selection signal from second to first order.",
        H("Diploid Dominance Selection Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("diploid-dominance-selection-order"),
            DeclarationHandle.Create(Declaration),
            H("Recessive selection is quadratic and exposed selection is linear"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Mean fitness and selected allele mass are constructed from the aa, ab, "
                        + "and bb genotype frequencies with fitnesses 1, 1-hs, and 1-s.")),
                Paragraph(Text(
                    "At h=0 the exact frequency change has a quadratic leading term and a "
                        + "cubic remainder. A nonzero product hs supplies a nonzero linear "
                        + "leading term, so the analytic order drops from two to one."))),
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
        Formula selection = F.Id("s");
        Formula dominance = F.Id("h");
        Formula point = F.Id("x");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula zero = D(0);
        Formula one = D(1);
        Formula two = D(2);
        Formula three = D(3);
        Formula pointSquared = new Formula.Power(point, Grp(two));
        Formula pointCubed = new Formula.Power(point, Grp(three));
        Formula oneMinusPoint = Subtract(one, point);
        Formula dominanceSelection = Multiply(dominance, selection);

        Formula typedDominance = Seq(dominance, Colon, Sp, reals);
        Formula typedPoint = Seq(point, Colon, Sp, reals);
        Formula meanAt = Call("meanFitness", dominance, point);
        Formula massAt = Call("selectedAlleleMass", dominance, point);
        Formula updatedAt = Call("updatedFrequency", dominance, point);
        Formula changeAt = Call("selectionChange", dominance, point);
        Formula meanDefinition = Add(
            Add(
                new Formula.Power(Seq(Open, oneMinusPoint, Close), Grp(two)),
                Multiply(
                    Multiply(Multiply(two, Grp(oneMinusPoint)), point),
                    Grp(Subtract(one, dominanceSelection)))),
            Multiply(pointSquared, Grp(Subtract(one, selection))));
        Formula massDefinition = Add(
            Multiply(pointSquared, Grp(Subtract(one, selection))),
            Multiply(
                Multiply(Grp(oneMinusPoint), point),
                Grp(Subtract(one, dominanceSelection))));
        Formula updatedDefinition = Fraction(massAt, meanAt);
        Formula changeDefinition = Subtract(updatedAt, point);
        Formula letDefinitions = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            Call("meanFitness", typedDominance, typedPoint),
            Sp, Colon, Eq, Sp, meanDefinition, Comma,
            RowBreak, Grp(),
            Call("selectedAlleleMass", typedDominance, typedPoint),
            Sp, Colon, Eq, Sp, massDefinition, Comma,
            RowBreak, Grp(),
            Call("updatedFrequency", typedDominance, typedPoint),
            Sp, Colon, Eq, Sp, updatedDefinition, Comma,
            RowBreak, Grp(),
            Call("selectionChange", typedDominance, typedPoint),
            Sp, Colon, Eq, Sp, changeDefinition,
            Close, SemiSpace);

        Formula recessiveChange = Call("selectionChange", zero, point);
        Formula recessiveMean = Call("meanFitness", zero, point);
        Formula recessiveLeading = Seq(
            Minus, Grp(Multiply(selection, pointSquared)));
        Formula recessiveExact = Fraction(
            Seq(Minus, Grp(Multiply(
                Multiply(selection, Grp(oneMinusPoint)), pointSquared))),
            Subtract(one, Multiply(selection, pointSquared)));
        Formula dominanceChange = Call("selectionChange", dominance, point);
        Formula dominanceLeading = Seq(
            Minus, Grp(Multiply(dominanceSelection, point)));
        Formula recessiveOrder = Call(
            "analyticOrderAt", Call("selectionChange", zero), zero);
        Formula dominanceOrder = Call(
            "analyticOrderAt", Call("selectionChange", dominance), zero);

        return Disp(Seq(
            Forall, Sp, selection, Comma, Sp, dominance, InMacro, Sp, reals, Comma,
            Sp, selection, Sp, Neq, Sp, zero, Sp, Rightarrow,
            RowBreak, Grp(), letDefinitions,
            RowBreak, Grp(),
            Open,
            Forall, Sp, point, InMacro, Sp, reals, Comma, Sp,
            recessiveMean, Sp, Neq, Sp, zero, Sp, Rightarrow, Sp,
            recessiveChange, Sp, Eq, Sp, recessiveExact,
            Close, Sp, Land,
            RowBreak, Grp(),
            Call("IsBigOAtZero", point,
                Subtract(recessiveChange, recessiveLeading), pointCubed), Sp, Land,
            RowBreak, Grp(),
            recessiveOrder, Sp, Eq, Sp, two, Sp, Land,
            RowBreak, Grp(),
            Call("IsBigOAtZero", point,
                Subtract(dominanceChange, dominanceLeading), pointSquared), Sp, Land,
            RowBreak, Grp(),
            Open,
            dominanceSelection, Sp, Neq, Sp, zero, Sp, Rightarrow, Sp,
            dominanceOrder, Sp, Eq, Sp, one,
            Close, Dot));
    }
}
