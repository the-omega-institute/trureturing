using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class InvariantConceptPrecludesOutcomeRemedyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/InvariantConceptPrecludesOutcomeRemedy."
            + "invariant_concept_precludes_outcome_remedy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An outcome computed from a concept preserved by every allowed action cannot "
            + "be changed to a different desired value.",
        H("Invariant Concepts Preclude Outcome Remedies"),
        Blocks(Describe.Lean(
            DescribeId.Create("invariant-concept-precludes-outcome-remedy"),
            DeclarationHandle.Create(Declaration),
            H("An invariant concept precludes a different outcome remedy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state transition is indexed by actions, and the allowed set is "
                        + "evaluated at the actual state. The outcome is constructed by "
                        + "applying j to the concept readout I.")),
                Paragraph(Text(
                    "Concept invariance transports through j, so every allowed action has "
                        + "the same outcome as the actual state.")),
                Paragraph(Text(
                    "Consequently, any desired outcome different from the actual outcome "
                        + "cannot be reached by an allowed action."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula action = F.Id("U");
        Formula conceptValue = F.Id("B");
        Formula outcome = F.Id("Y");
        Formula allowed = F.Id("A");
        Formula transition = F.Id("T");
        Formula concept = F.Id("I");
        Formula evaluate = F.Id("j");
        Formula actual = F.Id("x");
        Formula actionValue = F.Id("u");
        Formula desired = F.Id("yTarget");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula nextState = Apply(transition, actionValue, actual);
        Formula currentOutcome = Apply(evaluate, Apply(concept, actual));
        Formula nextOutcome = Apply(evaluate, Apply(concept, nextState));
        Formula actionAllowed = Seq(actionValue, Sp, InMacro, Sp, allowed);
        Formula conceptInvariant = Seq(
            Forall, Sp, Typed(actionValue, action), Comma, Sp,
            actionAllowed, Sp, Rightarrow, Sp,
            Apply(concept, nextState), Sp, Eq, Sp, Apply(concept, actual));
        Formula outcomeInvariant = Seq(
            Forall, Sp, Typed(actionValue, action), Comma, Sp,
            actionAllowed, Sp, Rightarrow, Sp,
            nextOutcome, Sp, Eq, Sp, currentOutcome);
        Formula reachesDesired = Seq(
            Exists, Sp, Typed(actionValue, action), Comma, Sp,
            actionAllowed, Sp, Land, Sp,
            nextOutcome, Sp, Eq, Sp, desired);
        Formula noDifferentRemedy = Seq(
            Forall, Sp, Typed(desired, outcome), Comma, Sp,
            desired, Sp, Neq, Sp, currentOutcome, Sp, Rightarrow, Sp,
            Neg, Open, reachesDesired, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, action, Comma, Sp,
                conceptValue, Comma, Sp, outcome), type), Comma, RowBreak, Grp(),
            Typed(allowed, Call("Set", action)), Comma, Sp,
            Typed(transition, Arrow(action, Arrow(state, state))), Comma, RowBreak, Grp(),
            Typed(concept, Arrow(state, conceptValue)), Comma, Sp,
            Typed(evaluate, Arrow(conceptValue, outcome)), Comma, Sp,
            Typed(actual, state), Comma, RowBreak, Grp(),
            Open, conceptInvariant, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, outcomeInvariant, Close, Sp, Land, RowBreak, Grp(),
            Open, noDifferentRemedy, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
