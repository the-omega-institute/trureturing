using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalOntology;

internal sealed class ActionExpansionIndistinguishabilityLawDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separating new action can make behavioral indistinguishability shrink strictly.",
        H("Action Expansion Indistinguishability Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("action-expansion-indistinguishability-law"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/OperationalOntology/"
                        + "ActionExpansionIndistinguishabilityLaw."
                        + "action_expansion_indistinguishability_law"),
                H("Action expansion reveals previously hidden distinctions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary action, state, and output carriers, agreement under every "
                            + "expanded action implies agreement under every original action.")),
                    Paragraph(Text(
                        "If a newly available action gives unequal public outputs on a pair from "
                            + "the original indistinguishability relation, that pair is absent from "
                            + "the expanded relation.")),
                    Paragraph(Text(
                        "The public countermodel uses empty and singleton Unit action sets with the "
                            + "identity Boolean transition. The same states belong to the original "
                            + "relation and fail to belong to the expanded relation, so the converse "
                            + "inclusion is not valid in general."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create(
                "D5/S3/ConceptDynamics/OperationalOntology/"
                    + "ActionExpansionIndistinguishability"))]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Relation(Formula allowed) =>
        Seq(Sim, Underscore, Grp(allowed));

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula original = F.Id("M");
        Formula expanded = Subscript(F.Id("M"), F.Id("expanded"));
        Formula act = F.Id("F");
        Formula observe = F.Id("O");
        Formula action = F.Id("u");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula actionSet = Call("Set", actionType);
        Formula actType = Arrow(actionType, Arrow(stateType, stateType));
        Formula observeType = Arrow(stateType, outputType);

        Formula forward = Seq(
            Relation(expanded), Sp, Subseteq, Sp, Relation(original));
        Formula newAction = Seq(
            Forall, Sp, action, InMacro, Sp,
            Grp(expanded, Sp, Setminus, Sp, original), Comma, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, stateType, Comma, Sp,
            x, Sp, Relation(original), Sp, y, Sp, Land, Sp,
            Apply(observe, Apply(Apply(act, action), x)), Sp, Neq, Sp,
            Apply(observe, Apply(Apply(act, action), y)), Sp, Rightarrow, Sp,
            Neg, Grp(x, Sp, Relation(expanded), Sp, y));

        Formula counterOriginal = Subscript(F.Id("M"), D(0));
        Formula counterExpanded = Subscript(F.Id("M"), D(1));
        Formula counterAct = Subscript(F.Id("F"), D(0));
        Formula counterObserve = Subscript(F.Id("O"), D(0));
        Formula counterX = Subscript(F.Id("x"), D(0));
        Formula counterY = Subscript(F.Id("y"), D(0));
        Formula countermodel = Seq(
            Exists, Sp, counterOriginal, Comma, Sp, counterExpanded,
            Colon, Sp, Call("Set", F.Id("Unit")), Comma, Sp,
            counterAct, Colon, Sp,
            Arrow(F.Id("Unit"), Arrow(F.Id("Bool"), F.Id("Bool"))), Comma, Sp,
            counterObserve, Colon, Sp, Arrow(F.Id("Bool"), F.Id("Bool")), Comma, Sp,
            counterX, Comma, Sp, counterY, Colon, Sp, F.Id("Bool"), Comma, Sp,
            counterOriginal, Sp, Subset, Sp, counterExpanded, Sp, Land, Sp,
            counterX, Sp, Relation(counterOriginal), Sp, counterY, Sp, Land, Sp,
            Neg, Grp(counterX, Sp, Relation(counterExpanded), Sp, counterY));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            original, Comma, Sp, expanded, Colon, Sp, actionSet, Comma, Sp,
            act, Colon, Sp, actType, Comma, Sp,
            observe, Colon, Sp, observeType, Comma, RowBreak, Grp(),
            original, Sp, Subseteq, Sp, expanded, Sp, Rightarrow, RowBreak, Grp(),
            Grp(forward), Sp, Land, RowBreak, Grp(),
            Grp(newAction), Sp, Land, RowBreak, Grp(),
            Grp(countermodel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
