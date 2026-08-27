using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class PositiveConditioningPredictionStabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal discrete future laws remain equal after conditioning on a positive next outcome.",
        H("Positive Conditioning Preserves Predictive Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-equivalence-survives-positive-conditioning"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/"
                        + "PositiveConditioningPredictionStability."
                        + "predictive_equivalence_preserved_by_positive_conditioning"),
                H("Predictive equivalence survives positive conditioning"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A history, action, and future protocol determine a finite joint law "
                            + "of the next observation and the remaining future record. Its "
                            + "first-coordinate marginal is the next-observation law.")),
                    Paragraph(Text(
                        "The history-extension equation identifies every future law after an "
                            + "observed outcome with the repository's canonical conditional of "
                            + "that joint law.")),
                    Paragraph(Text(
                        "Equal predictive profiles give equal numerators and denominators. "
                            + "Positive outcome mass makes both denominators nonzero, so the "
                            + "conditional future laws agree for every later protocol."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StabilityFormula()
    {
        Formula historyType = F.Id("H");
        Formula actionType = F.Id("A");
        Formula observationType = F.Id("Y");
        Formula protocolType = F.Id("W");
        Formula recordType = F.Id("Z");
        Formula jointLaw = F.Id("J");
        Formula outcomeLaw = F.Id("p");
        Formula futureLaw = F.Id("K");
        Formula extend = F.Id("e");
        Formula history = F.Id("h");
        Formula otherHistory = Seq(F.Id("h"), Apos);
        Formula action = F.Id("a");
        Formula otherAction = Seq(F.Id("a"), Apos);
        Formula observation = F.Id("y");
        Formula protocol = F.Id("w");
        Formula record = F.Id("z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula jointCarrier = new Formula.TypeArrow(
            Seq(observationType, Sp, Times, Sp, recordType), real);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(historyType, Comma, Sp, actionType, Comma, Sp,
                    observationType, Comma, Sp, protocolType, Comma, Sp, recordType),
                type), Comma, RowBreak, Grp(),
            Call("Finite", recordType), Comma, RowBreak, Grp(),
            Typed(jointLaw,
                new Formula.TypeArrow(historyType,
                    new Formula.TypeArrow(actionType,
                        new Formula.TypeArrow(protocolType, jointCarrier)))),
            Comma, RowBreak, Grp(),
            Typed(outcomeLaw,
                new Formula.TypeArrow(historyType,
                    new Formula.TypeArrow(actionType,
                        new Formula.TypeArrow(observationType, real)))),
            Comma, RowBreak, Grp(),
            Typed(futureLaw,
                new Formula.TypeArrow(historyType,
                    new Formula.TypeArrow(protocolType,
                        new Formula.TypeArrow(recordType, real)))),
            Comma, RowBreak, Grp(),
            Typed(extend,
                new Formula.TypeArrow(historyType,
                    new Formula.TypeArrow(actionType,
                        new Formula.TypeArrow(observationType, historyType)))),
            Comma, RowBreak, Grp(),
            Open, Forall, Sp,
            Typed(history, historyType), Comma, Sp,
            Typed(action, actionType), Comma, Sp,
            Typed(protocol, protocolType), Comma, Sp,
            Call("marginal", Apply(jointLaw, history, action, protocol)), Sp, Eq, Sp,
            Apply(outcomeLaw, history, action), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp,
            Typed(history, historyType), Comma, Sp,
            Typed(action, actionType), Comma, Sp,
            Typed(observation, observationType), Comma, Sp,
            Typed(protocol, protocolType), Comma, Sp,
            Typed(record, recordType), Comma, RowBreak, Grp(),
            Apply(futureLaw, Apply(extend, history, action, observation), protocol, record),
            Sp, Eq, Sp,
            Call("conditional", Apply(jointLaw, history, action, protocol),
                observation, record), Close, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp,
            Typed(Seq(history, Comma, Sp, otherHistory), historyType), Comma, Sp,
            Typed(action, actionType), Comma, Sp,
            Typed(observation, observationType), Comma, RowBreak, Grp(),
            Open, Forall, Sp,
            Typed(otherAction, actionType), Comma, Sp,
            Typed(protocol, protocolType), Comma, Sp,
            Apply(jointLaw, history, otherAction, protocol), Sp, Eq, Sp,
            Apply(jointLaw, otherHistory, otherAction, protocol), Close,
            Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Apply(outcomeLaw, history, action, observation),
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(protocol, protocolType), Comma, Sp,
            Apply(futureLaw, Apply(extend, history, action, observation), protocol),
            Sp, Eq, Sp,
            Apply(futureLaw, Apply(extend, otherHistory, action, observation), protocol), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
