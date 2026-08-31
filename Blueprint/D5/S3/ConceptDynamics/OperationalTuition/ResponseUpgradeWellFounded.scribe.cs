using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class ResponseUpgradeWellFoundedDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite T2-compliant response traces cannot retry forever: a sufficiently long "
            + "same-stimulus trace must stop or change class, and blind retries are decidable.",
        H("Response Upgrade Well-Foundedness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("t2-response-trace-must-stop-or-change-class"),
                DeclarationHandle.Create(Prefix + "t2_response_upgrade_well_founded"),
                H("T2 response traces stop or change class"),
                StatementSource.FromAuthor(UpgradeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A response event records a stimulus, response class, response value, "
                            + "and an explicit stop bit. T2 compliance is a structural predicate "
                            + "requiring the nonterminal responses in each finite stimulus/class "
                            + "slice to be duplicate-free.")),
                    Paragraph(Text(
                        "The finite response alphabet bounds every duplicate-free list by its "
                            + "Fintype cardinality. If a same-stimulus trace exceeds that bound, "
                            + "the compliant trace therefore contains a stopping event or an event "
                            + "whose response class has changed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blind-retry-violation-is-decidable"),
                DeclarationHandle.Create(Prefix + "t2_violation_decidable"),
                H("Blind-retry T2 violations are decidable"),
                StatementSource.FromAuthor(DecisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All carriers and the finite trace are explicit, so the universal T2 "
                            + "predicate has a decision procedure. The Boolean classifier returns "
                            + "true exactly for its negation.")),
                    Paragraph(Text(
                        "A two-event trace repeating the sole response in a one-element alphabet "
                            + "is a compiled blind-retry witness and is classified as a violation."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula Event(Formula stimulus, Formula responseClass, Formula response) =>
        Call("ResponseEvent", stimulus, responseClass, response);

    private static Formula UpgradeFormula()
    {
        Formula stimulusType = F.Id("S");
        Formula classType = F.Id("C");
        Formula responseType = F.Id("R");
        Formula trace = F.Id("trace");
        Formula stimulus = F.Id("stimulus");
        Formula responseClass = F.Id("responseClass");
        Formula evt = F.Id("event");
        Formula eventType = Event(stimulusType, classType, responseType);
        Formula sameStimulus = Seq(
            Forall, Sp, evt, Colon, Sp, eventType, Comma, Sp,
            evt, Sp, InMacro, Sp, trace, Sp, Rightarrow, Sp,
            Call("stimulus", evt), Sp, Eq, Sp, stimulus);
        Formula upgrade = Seq(
            Exists, Sp, evt, Comma, Sp, evt, Sp, InMacro, Sp, trace, Sp, Land, Sp,
            Open, Call("stopped", evt), Sp, Eq, Sp, F.Id("true"), Sp, Lor, Sp,
            Call("responseClass", evt), Sp, Neq, Sp, responseClass, Close);
        Formula longTrace = Seq(
            Call("card", responseType), Sp, Lt, Sp, Call("length", trace));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, stimulusType, Comma, Sp, classType, Comma, Sp,
                responseType, Colon, Sp, F.Id("Type"), Comma),
            Seq(Grp(), Typeclass("Fintype", stimulusType), Comma,
                Sp, Typeclass("Fintype", classType), Comma,
                Sp, Typeclass("Fintype", responseType), Comma),
            Seq(Grp(), Typeclass("DecidableEq", stimulusType), Comma,
                Sp, Typeclass("DecidableEq", classType), Comma,
                Sp, Typeclass("DecidableEq", responseType), Comma),
            Seq(trace, Colon, Sp, Call("List", eventType), Comma),
            Seq(stimulus, Colon, Sp, stimulusType, Comma, Sp,
                responseClass, Colon, Sp, classType, Comma),
            Seq(Call("T2Compliant", trace), Sp, Rightarrow, Sp,
                sameStimulus, Sp, Rightarrow, Sp, longTrace, Sp, Rightarrow, Sp,
                upgrade, Dot),
        ]));
    }

    private static Formula DecisionFormula()
    {
        Formula stimulusType = F.Id("S");
        Formula classType = F.Id("C");
        Formula responseType = F.Id("R");
        Formula trace = F.Id("trace");
        Formula eventType = Event(stimulusType, classType, responseType);
        Formula decision = Seq(
            Call("t2ViolationDecision", trace), Sp, Eq, Sp, F.Id("true"), Sp,
            Iff, Sp, Neg, Sp, Call("T2Compliant", trace));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, stimulusType, Comma, Sp, classType, Comma, Sp,
                responseType, Colon, Sp, F.Id("Type"), Comma),
            Seq(Grp(), Typeclass("Fintype", stimulusType), Comma,
                Sp, Typeclass("Fintype", classType), Comma,
                Sp, Typeclass("DecidableEq", stimulusType), Comma,
                Sp, Typeclass("DecidableEq", classType), Comma,
                Sp, Typeclass("DecidableEq", responseType), Comma),
            Seq(trace, Colon, Sp, Call("List", eventType), Comma),
            Seq(decision, Dot),
        ]));
    }
}
