using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalOntology;

internal sealed class ActionExpansionIndistinguishabilityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "More allowed actions can only remove behavioral identifications.",
        H("Action Expansion and Indistinguishability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("action-indistinguishability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "actionIndistinguishability"),
                H("Behavioral indistinguishability under allowed actions"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two states are behaviorally indistinguishable for an allowed action set "
                        + "when every action in that set produces equal public readouts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("action-expansion-shrinks-indistinguishability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "action_expansion_shrinks_indistinguishability"),
                H("Action expansion shrinks indistinguishability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The action map and public readout are independent source primitives. "
                            + "The two relations use the same state, action, and output carriers.")),
                    Paragraph(Text(
                        "If the original allowed actions are contained in the expanded set, every "
                            + "pair agreeing after all expanded actions also agrees after each "
                            + "original action.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the exact bounded-intersection inclusion lemma; "
                            + "the Lean theorem is a thin application to the equal-output relations."))),
                DescribeRole.Theorem))));

    private static Formula Relation(Formula allowed) =>
        Seq(Sim, Underscore, Grp(allowed));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ApplyAction(Formula action, Formula state) =>
        Seq(F.Id("F"), Underscore, Grp(action), Open, state, Close);

    private static Formula DefinitionFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula action = F.Id("m");
        Formula allowed = F.Id("M");
        Formula observe = F.Id("O");

        return Disp(Seq(
            x, Sp, Relation(allowed), Sp, y, Sp, Leftrightarrow, Sp,
            Forall, Sp, action, InMacro, Sp, allowed, Comma, Sp,
            Apply(observe, ApplyAction(action, x)), Sp, Eq, Sp,
            Apply(observe, ApplyAction(action, y)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula original = F.Id("M");
        Formula expanded = Seq(
            F.Id("M"), Underscore, Grp(Mathrm, Grp(F.Id("expanded"))));
        Formula act = F.Id("F");
        Formula observe = F.Id("O");
        Formula actionMap = Seq(actionType, Sp, To, Sp, stateType, Sp, To, Sp, stateType);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            original, Comma, Sp, expanded, Subset, Sp, actionType, Comma, Sp,
            act, Colon, Sp, actionMap, Comma, Sp,
            observe, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma,
            RowBreak, Grp(),
            original, Subseteq, Sp, expanded, Sp, Rightarrow, RowBreak, Grp(),
            Relation(expanded), Subseteq, Sp, Relation(original), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
