using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class ControlIdentityRefinesPassiveDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Control/ControlIdentityRefinesPassive.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding control actions refines action-induced identity, while passive identity need "
            + "not recover the full control identity.",
        H("Control Identity Refines Passive Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("control-identity-refines-passive-identity"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "control_identity_refines_passive"),
                H("Control identity refines passive identity"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The action identity of a state is the complete family of observed "
                            + "outcomes obtained after applying every action in the chosen set. "
                            + "When every passive action is also a control action, restricting "
                            + "that family from control coordinates to passive coordinates "
                            + "provides the required factor map.")),
                    Paragraph(Text(
                        "Thus the full-control identity refines the passive identity. Equally, "
                            + "states that agree after every control action must agree after "
                            + "every passive action, so control indistinguishability is contained "
                            + "in passive indistinguishability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-control-refinement-can-fail"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "reverse_control_refinement_can_fail"),
                H("Passive identity need not recover control identity"),
                StatementSource.FromAuthor(ReverseFailureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the two-state Boolean system, the sole passive action resets every "
                        + "state to false, whereas the additional control action preserves the "
                        + "state. The passive readout therefore identifies false and true, but "
                        + "the control readout separates them. Forward refinement still holds, "
                        + "while no factor map can reconstruct the control identity from the "
                        + "passive one."))),
                DescribeRole.Lemma))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Indistinguishability(Formula actions) =>
        Seq(Sim, Underscore, Grp(actions));

    private static Formula ActionIdentity(Formula actions) =>
        Subscript(F.Id("I"), actions);

    private static Formula RefinementFormula()
    {
        Formula actionType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula passive = F.Id("P");
        Formula control = F.Id("C");
        Formula act = F.Id("act");
        Formula observe = F.Id("obs");

        return Disp(Seq(
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, F.Id("Type"), Comma, Sp,
            passive, Comma, Sp, control, Colon, Sp, Call("Set", actionType), Comma,
            RowBreak, Grp(),
            act, Colon, Sp, actionType, Sp, To, Sp, stateType, Sp, To, Sp, stateType,
            Comma, Sp,
            observe, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma,
            RowBreak, Grp(),
            passive, Sp, Subseteq, Sp, control, Sp, Rightarrow, Sp,
            Refines(ActionIdentity(passive), ActionIdentity(control)), Sp, Land, Sp,
            Indistinguishability(control), Sp, Subseteq, Sp,
            Indistinguishability(passive), Dot));
    }

    private static Formula ReverseFailureFormula()
    {
        Formula actionType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula boolType = F.Id("Bool");
        Formula passive = F.Id("P");
        Formula control = F.Id("C");
        Formula action = F.Id("a");
        Formula state = F.Id("x");
        Formula act = F.Id("act");
        Formula observe = F.Id("obs");
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula passiveSet = Seq(OpenBrace, Grp(falseValue), CloseBrace);
        Formula controlSet = Seq(
            OpenBrace, Grp(falseValue), Comma, Sp, Grp(trueValue), CloseBrace);

        return Disp(Seq(
            actionType, Sp, Eq, Sp, stateType, Sp, Eq, Sp, outputType, Sp, Eq, Sp,
            boolType, Comma, Sp,
            passive, Sp, Eq, Sp, passiveSet, Comma, Sp,
            control, Sp, Eq, Sp, controlSet, Comma,
            RowBreak, Grp(),
            act, Open, action, Comma, Sp, state, Close, Sp, Eq, Sp,
            Call("ite", action, state, falseValue), Comma, Sp,
            observe, Sp, Eq, Sp, F.Id("id"), Comma,
            RowBreak, Grp(), Rightarrow, Sp,
            passive, Sp, Subseteq, Sp, control, Sp, Land, Sp,
            Refines(ActionIdentity(passive), ActionIdentity(control)), Sp, Land, Sp,
            Neg, Sp, Refines(ActionIdentity(control), ActionIdentity(passive)), Dot));
    }
}
