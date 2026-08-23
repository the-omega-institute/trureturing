using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ActionStateRightsSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Empty action states separate non-infringement from positive realization.",
        H("Negative and Positive Rights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-action-state-separates-rights"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ActionStateRightsSeparation."
                        + "no_action_state_separates_rights"),
                H("No available action separates the two rights"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An allowed-action set, a chosen-action set, a transition, and a goal "
                            + "set are the source primitives. A negative right is disjointness "
                            + "from the chosen actions; a positive right requires an allowed "
                            + "transition into the goal.")),
                    Paragraph(Text(
                        "When the allowed-action set is empty and chosen actions are restricted "
                            + "to it, every forbidden subset is harmless, while the positive goal "
                            + "and its realization condition both fail outside the goal.")),
                    Paragraph(Text(
                        "The four public conjuncts expose the negative-right clause, positive "
                            + "failure, realization failure, and non-equivalence of the predicates."))),
                DescribeRole.Theorem))));

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

    private static Formula SeparationFormula()
    {
        Formula stateType = F.Id("State");
        Formula actionType = F.Id("Action");
        Formula state = F.Id("x");
        Formula allowed = new Formula.Subscript(F.Id("U"), state);
        Formula chosen = new Formula.Subscript(F.Id("V"), state);
        Formula forbidden = F.Id("N");
        Formula step = F.Id("F");
        Formula goal = F.Id("G");
        Formula setAction = Seq(Operatorname, Grp(F.Id("Set")), Sp, actionType);
        Formula setState = Seq(Operatorname, Grp(F.Id("Set")), Sp, stateType);
        Formula negative = Apply(
            Seq(Operatorname, Grp(F.Id("negativeRight"))), forbidden, chosen);
        Formula positive = Apply(
            Seq(Operatorname, Grp(F.Id("positiveRight"))),
            allowed, step, goal, state);
        Formula noForbidden = Seq(
            Forall, Sp, forbidden, Colon, Sp, setAction,
            Comma, Sp, forbidden, Sp, Subseteq, Sp, allowed,
            Sp, Rightarrow, Sp, negative);
        Formula types = Seq(
            stateType, Comma, Sp, actionType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")));
        return Disp(Seq(
            Forall, Sp, types, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            allowed, Comma, Sp, chosen, Colon, Sp, setAction, Comma, Sp,
            step, Colon, Sp, actionType, Sp, To, Sp, stateType, Sp, To, Sp,
            stateType, Comma, Sp,
            goal, Colon, Sp, setState, Comma, Esc,
            chosen, Sp, Subseteq, Sp, allowed, Sp, Rightarrow, Esc,
            allowed, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Esc,
            Neg, Sp, Grp(state, Sp, InMacro, Sp, goal), Sp, Rightarrow, Esc,
            Grp(noForbidden), Sp, Land, Sp, Neg, Sp, positive, Sp, Land, Sp,
            Neg, Sp, Grp(Seq(state, Sp, InMacro, Sp, goal, Sp, Lor, Sp, positive)), Sp,
            Land, Sp, Neg, Sp,
            Grp(Seq(Grp(noForbidden), Sp, Iff, Sp, positive)), Dot));
    }
}
