using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class BeliefSetSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal compatible belief sets determine equal future observation trajectories.",
        H("Belief Set Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compatible-belief-set-is-sufficient-for-future-trajectories"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/BeliefSetSufficiency."
                        + "belief_set_sufficiency"),
                H("The compatible belief set is sufficient for future trajectories"),
                StatementSource.FromAuthor(SufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be the hidden-state type, U the action type, and O the observation "
                            + "type. The compatible belief set starts with every state having the "
                            + "initial observation, then processes each action-observation pair by "
                            + "applying the indexed update and retaining exactly the states with the "
                            + "reported next observation.")),
                    Paragraph(Text(
                        "For a future action word, the observation trajectory of a state reads the "
                            + "canonical controlled behavior on every prefix of that word. Possible "
                            + "trajectories are constructed independently from hidden start and final "
                            + "states connected by every observed transition in the concrete history.")),
                    Paragraph(Text(
                        "If two concrete histories generate the same compatible belief set, their "
                            + "possible trajectory sets are equal for every future action word. The statement "
                            + "retains both histories publicly. The proof first identifies the final "
                            + "states produced by the recursive belief update with those produced by "
                            + "the independent transition-path relation.")),
                    Paragraph(Text(
                        "The module directly reuses the repository's `controlledBehavior` semantics "
                            + "and pinned Mathlib's exact `List.inits` prefix construction. Searches "
                            + "found no existing theorem combining them with recursively updated belief "
                            + "sets."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula SufficiencyFormula()
    {
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("U");
        Formula observationType = F.Id("O");
        Formula update = F.Id("F");
        Formula observe = F.Id("q");
        Formula initialFirst = Subscript(F.Id("o"), D(1));
        Formula initialSecond = Subscript(F.Id("o"), D(2));
        Formula historyFirst = Subscript(F.Id("h"), D(1));
        Formula historySecond = Subscript(F.Id("h"), D(2));
        Formula futureActions = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula list = Seq(Operatorname, Grp(F.Id("List")));
        Formula belief = Seq(Operatorname, Grp(F.Id("compatibleBelief")));
        Formula possible = Seq(Operatorname,
            Grp(F.Id("possibleObservationTrajectories")));
        Formula actionList = Apply(list, actionType);
        Formula historyType = Apply(list,
            Seq(actionType, Sp, Times, Sp, observationType));
        Formula firstBelief = Apply(belief, update, observe,
            initialFirst, historyFirst);
        Formula secondBelief = Apply(belief, update, observe,
            initialSecond, historySecond);
        Formula firstPossible = Apply(possible, update, observe,
            initialFirst, historyFirst, futureActions);
        Formula secondPossible = Apply(possible, update, observe,
            initialSecond, historySecond, futureActions);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, actionType, Comma, Sp,
            observationType, Colon, Sp, type, Comma, RowBreak,
            Typed(update, new Formula.TypeArrow(actionType,
                new Formula.TypeArrow(stateType, stateType))), Comma, Sp,
            Typed(observe, new Formula.TypeArrow(stateType, observationType)), Comma, RowBreak,
            Typed(Seq(initialFirst, Comma, Sp, initialSecond), observationType), Comma, Sp,
            Typed(Seq(historyFirst, Comma, Sp, historySecond), historyType), Comma, RowBreak,
            firstBelief, Sp, Eq, Sp, secondBelief, Sp, Rightarrow, RowBreak,
            Forall, Sp, Typed(futureActions, actionList), Comma, Sp,
            firstPossible, Sp, Eq, Sp, secondPossible, Dot,
            End, Grp(F.Id("gathered"))));
    }

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

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
