using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class SeenDirectionAndAppendCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample."
            + "admissible_judge_early_append_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An early ledger append can flip admission when it is not strictly after the "
            + "snapshot decision event.",
        H("Early Append Counterexample"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-judge-early-append-witness"),
                DeclarationHandle.Create(Declaration),
                H("The strict post-decision premise is necessary"),
                StatementSource.FromAuthor(EarlyAppendWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The semantic neighbor uses an old ledger containing an adjudication "
                            + "event and an extended ledger formed by appending a generate event "
                            + "with event id equal to the snapshot decision event. Its dependency "
                            + "touches the commitment closure: the old judge is admissible, while "
                            + "the extended judge is rejected by AdaptiveUseInClosure. This is "
                            + "the required concrete counterexample to dropping the strict "
                            + "post-decision condition."))),
                DescribeRole.Theorem))));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula EarlyAppendWitnessFormula()
    {
        Formula falseValue = F.Id("false");
        Formula oldLedger = F.Id("semanticOldLedger");
        Formula extendedLedger = F.Id("semanticExtendedLedger");
        Formula semanticSnapshot = F.Id("semanticSnapshot");
        Formula adaptiveEvent = F.Id("semanticAdaptiveEvent");
        Formula oldAdmitted = Call(
            "AdmissibleJudge",
            oldLedger,
            semanticSnapshot,
            F.Id("semanticOldValid"),
            falseValue);
        Formula extendedRejected = new Formula.Not(Call(
            "AdmissibleJudge",
            extendedLedger,
            semanticSnapshot,
            F.Id("semanticExtendedValid"),
            falseValue));
        Formula appendEquality = Equal(
            Call("events", extendedLedger),
            Call(
                "append",
                Call("events", oldLedger),
                Call("singletonList", adaptiveEvent)));
        Formula earlyEvent = LessThanOrEqual(
            Call("eventId", adaptiveEvent),
            Call("decisionEvent", semanticSnapshot));
        Formula touchesClosure = Call(
            "Nonempty",
            Call(
                "intersection",
                Call("dependencies", adaptiveEvent),
                Call("dependencyClosure", semanticSnapshot)));
        return F.Disp(And(
            oldAdmitted,
            And(
                extendedRejected,
                And(appendEquality, And(earlyEvent, touchesClosure)))));
    }
}
