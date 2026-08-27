using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class PredictiveStateUnifilarUpdateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUnifilarUpdate."
            + "unifilar_predictive_update";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete future laws induce an almost-sure single-valued predictive-state update.",
        H("Predictive-State Unifilar Update"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-future-law-quotient-has-unifilar-update"),
                DeclarationHandle.Create(Declaration),
                H("The complete-future-law quotient has a unifilar update"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each history is assigned a probability measure on infinite symbol "
                            + "streams. Histories with the same full measure define one "
                            + "predictive state.")),
                    Paragraph(Text(
                        "For a positive first-symbol cylinder, extending the history is "
                            + "required to realize the normalized restriction to that cylinder, "
                            + "pushed forward by the tail map. This is the public process "
                            + "consistency premise.")),
                    Paragraph(Text(
                        "The constructed quotient update sends every positive symbol to the "
                            + "class of the extended history. Countability of the symbol carrier "
                            + "then turns that pointwise rule into the displayed almost-everywhere "
                            + "next-symbol statement."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LambdaFormula(Formula variable, Formula body) =>
        Seq(Lambda, Sp, variable, Comma, Sp, body);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula historyType = F.Id("History");
        Formula symbolType = F.Id("Symbol");
        Formula naturals = F.Id("Nat");
        Formula futureType = Arrow(naturals, symbolType);
        Formula lawType = Call("ProbabilityMeasure", futureType);
        Formula futureLaw = F.Id("K");
        Formula extend = F.Id("extend");
        Formula update = F.Id("T");
        Formula history = F.Id("h");
        Formula symbol = F.Id("a");
        Formula future = F.Id("x");
        Formula index = F.Id("n");
        Formula quotient = Call("Quotient", Call("ker", futureLaw));
        Formula lawAtHistory = Call("toMeasure", Apply(futureLaw, history));
        Formula cylinder = Call(
            "setOf",
            LambdaFormula(future, Equal(Apply(future, D(0)), symbol)));
        Formula cylinderMass = Apply(lawAtHistory, cylinder);
        Formula tail = LambdaFormula(
            Seq(future, Sp, index),
            Apply(future, Seq(index, Sp, Plus, Sp, D(1))));
        Formula conditionedTail = Call(
            "scale",
            Call("inverse", cylinderMass),
            Call("map", tail, Call("restrict", lawAtHistory, cylinder)));
        Formula conditioned = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", historyType), Bound("a", symbolType)],
            Implies(
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, cylinderMass),
                Equal(
                    Call("toMeasure", Apply(futureLaw, Apply(extend, history, symbol))),
                    conditionedTail)));
        Formula projection = Call("quotientClass", futureLaw, history);
        Formula extendedProjection = Call(
            "quotientClass", futureLaw, Apply(extend, history, symbol));
        Formula computation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", historyType), Bound("a", symbolType)],
            Implies(
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, cylinderMass),
                Equal(Apply(update, projection, symbol), extendedProjection)));
        Formula marginal = Call(
            "map",
            LambdaFormula(future, Apply(future, D(0))),
            lawAtHistory);
        Formula almostEverywhere = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", historyType)],
            Call(
                "AlmostEverywhere",
                marginal,
                LambdaFormula(
                    symbol,
                    Equal(Apply(update, projection, symbol), extendedProjection))));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("T", Arrow(quotient, Arrow(symbolType, quotient)))],
            And(computation, almostEverywhere));
        Formula instances = And(
            Call("MeasurableSpace", symbolType),
            And(
                Call("MeasurableSingletonClass", symbolType),
                Call("Countable", symbolType)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("History", type),
                Bound("Symbol", type),
                Bound("K", Arrow(historyType, lawType)),
                Bound("extend", Arrow(historyType, Arrow(symbolType, historyType))),
            ],
            Implies(And(instances, conditioned), conclusion)));
    }
}
