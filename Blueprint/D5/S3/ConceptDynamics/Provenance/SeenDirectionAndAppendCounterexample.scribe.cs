using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class SeenDirectionAndAppendCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample."
            + "role_admission_direction_nonvacuity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction witnesses distinguish outgoing contamination from incoming dependency "
            + "closures, and an early ledger append flips admission.",
        H("Access Direction and Early Append Witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("role-admission-direction-nonvacuity"),
                DeclarationHandle.Create(Declaration),
                H("The direction and append boundaries are non-vacuous"),
                StatementSource.FromAuthor(DirectionNonvacuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The concrete two-element edge false -> true puts true in outgoing "
                            + "Contam of {false} and puts false in the incoming artifact "
                            + "dependency closure of {true}. Independently, the evidence "
                            + "filtration supplies a monotone seen set in which the required "
                            + "evidence dependency is visible at the freeze event.")),
                    Paragraph(Text(
                        "Reversing that edge removes false from the same one-step seen prefix, "
                            + "so the direction claim is not a naming convention or a constant "
                            + "set. The aggregate theorem consumes all three named direction "
                            + "witnesses.")),
                    Paragraph(Text(
                        "The semantic neighbor uses an old ledger containing an adjudication "
                            + "event and an extended ledger formed by appending a generate event "
                            + "with event id equal to the snapshot decision event. Its dependency "
                            + "touches the commitment closure: the old judge is admissible, while "
                            + "the extended judge is rejected by AdaptiveUseInClosure. This is "
                            + "the required concrete counterexample to dropping the strict "
                            + "post-decision condition."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Contam(Formula relation, Formula roots) =>
        Call("Contam", relation, roots);

    private static Formula Singleton(Formula value) =>
        new Formula.SetLiteral([value]);

    private static Formula DirectionNonvacuityFormula()
    {
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula direction = F.Id("directionRelation");
        Formula snapshot = F.Id("directionSnapshot");

        Formula contamDirection = And(
            Member(trueValue, Contam(direction, Singleton(falseValue))),
            new Formula.Not(Member(
                falseValue,
                Contam(direction, Singleton(trueValue)))));

        Formula artifactIncoming =
            Member(falseValue, Call("dependencyClosure", snapshot));
        Formula evidenceIncoming =
            Member(falseValue, Call("evidenceDependencies", snapshot));
        Formula evidenceVisible = Member(
            falseValue,
            Apply(
                Call("seen", Call("filtration", snapshot)),
                Call("freezeEvent", snapshot)));
        Formula notOutgoing = new Formula.Not(Member(
            falseValue,
            Contam(direction, Call("commitmentRoots", snapshot))));
        Formula dependencyDirection = And(
            artifactIncoming,
            And(evidenceIncoming, And(evidenceVisible, notOutgoing)));

        Formula seenDirection = And(
            Member(falseValue, Apply(Call("seen", F.Id("seenForward")), Num(1))),
            And(
                new Formula.Not(Member(
                    falseValue,
                    Apply(Call("seen", F.Id("seenReverse")), Num(1)))),
                new Formula.Not(Member(
                    falseValue,
                    Apply(Call("seen", F.Id("seenForward")), Num(0))))));

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
        Formula appendBoundary = And(
            oldAdmitted,
            And(
                extendedRejected,
                And(appendEquality, And(earlyEvent, touchesClosure))));

        return F.Disp(And(
            contamDirection,
            And(dependencyDirection, And(seenDirection, appendBoundary))));
    }
}
