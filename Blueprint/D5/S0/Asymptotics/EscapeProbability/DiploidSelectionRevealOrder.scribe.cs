using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class DiploidSelectionRevealOrderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Asymptotics/EscapeProbability/DiploidSelectionRevealOrder."
            + "diploid_selection_reveal_order";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive heterozygote effect changes the rare-allele signal from second to first order.",
        H("Diploid Selection Reveal Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("diploid-selection-reveal-order"),
            DeclarationHandle.Create(Declaration),
            H("Complete recessivity is quadratic and positive dominance is linear"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Mean fitness, selected allele mass, updated frequency, and selection "
                        + "change are the source's diploid genotype formulas with fitnesses "
                        + "1, 1-hs, and 1-s.")),
                Paragraph(Text(
                    "For nonzero s, complete recessivity has the displayed exact change, a "
                        + "cubic remainder after its quadratic leading term, and analytic "
                        + "order two. Under h greater than zero, the exposed change has a "
                        + "quadratic remainder after its linear leading term and analytic "
                        + "order one."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder")),
        ]));

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
        Formula recessiveLeading = Seq(Minus, Grp(Multiply(selection, pointSquared)));
        Formula recessiveExact = Fraction(
            Seq(Minus, Grp(Multiply(
                Multiply(selection, Grp(oneMinusPoint)), pointSquared))),
            Subtract(one, Multiply(selection, pointSquared)));
        Formula exposedChange = Call("selectionChange", dominance, point);
        Formula exposedLeading = Seq(Minus, Grp(Multiply(dominanceSelection, point)));
        Formula recessiveOrder = Call(
            "analyticOrderAt", Call("selectionChange", zero), zero);
        Formula exposedOrder = Call(
            "analyticOrderAt", Call("selectionChange", dominance), zero);
        Formula positiveDominance = Seq(zero, Sp, Lt, Sp, dominance);
        Formula exposedRemainder = Call(
            "IsBigOAtZero", point,
            Subtract(exposedChange, exposedLeading), pointSquared);

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
            Open, positiveDominance, Sp, Rightarrow, Sp,
            exposedRemainder, Close, Sp, Land,
            RowBreak, Grp(),
            Open, positiveDominance, Sp, Rightarrow, Sp,
            exposedOrder, Sp, Eq, Sp, one, Close, Dot));
    }
}
