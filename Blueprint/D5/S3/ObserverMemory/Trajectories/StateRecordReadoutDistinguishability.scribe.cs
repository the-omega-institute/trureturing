using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class StateRecordReadoutDistinguishabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Abstract histories preserve endpoint collapse and conditional record separation.",
        H("State and Record Readout Distinguishability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("state-record-readout-distinguishability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/"
                        + "StateRecordReadoutDistinguishability."
                        + "state_record_readout_distinguishability"),
                H("State readouts merge; record readouts separate conditionally"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Lambda1 be a record type equipped with named AppendOnlyOps: append, "
                            + "a monotonic prefix relation, and a certificate that append preserves "
                            + "that relation. Let O be a RecordedObserver with q1 : X -> A, the "
                            + "controlled update T1 : X x Y2 -> X, and q2 : Lambda1 -> Y2.")),
                    Paragraph(Text(
                        "Let H be an abstract history carrier. A HistoryEvolution E supplies an "
                            + "advance operation and an observation H -> X x Lambda1, with a law "
                            + "identifying the observation after advance with the source one-step "
                            + "evolution. Endpoint and recordImage are the two projections of that "
                            + "single certified observation.")),
                    Paragraph(Text(
                        "Let two histories in H have the same endpoint x and respective "
                            + "record images lambda and lambdaPrime, with the images distinct.")),
                    Paragraph(Text(
                        "The first public conjunct quantifies over every state-only readout s. "
                            + "Since both histories end at x, their state readout values are equal.")),
                    Paragraph(Text(
                        "The second public conjunct is an equivalence. The composed history "
                            + "readout q2 after the record-image map lies outside its equality "
                            + "kernel exactly when q2(lambda) and q2(lambdaPrime) differ. Thus "
                            + "its two directions are the source's two record-separation assertions.")),
                    Paragraph(Text(
                        "The theorem does not claim that q2 separates every pair of distinct "
                            + "records. A constant q2 makes both sides of the equivalence false, "
                            + "as required by the source's conditional wording."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula recordType = new Formula.Subscript(F.Id("Lambda"), D(1));
        Formula readingType = F.Id("A");
        Formula stateOutputType = F.Id("Y");
        Formula recordOutputType = new Formula.Subscript(F.Id("Y"), D(2));
        Formula historyType = F.Id("H");
        Formula recordOpsType = Call("AppendOnlyOps", recordType, readingType);
        Formula recordOps = F.Id("R");
        Formula observerType =
            Call("RecordedObserver", stateType, recordType, readingType, recordOutputType, recordOps);
        Formula observer = F.Id("O");
        Formula historyOpsType =
            Call("HistoryEvolution", historyType, stateType, recordType, readingType,
                recordOutputType, recordOps, observer);
        Formula historyOps = F.Id("E");
        Formula endpoint = Call("endpoint", historyOps);
        Formula recordImage = Call("recordImage", historyOps);
        Formula recordReadout = Call("q2", observer);
        Formula first = F.Id("gamma");
        Formula second = F.Id("gammaPrime");
        Formula state = F.Id("x");
        Formula firstRecord = F.Id("lambda");
        Formula secondRecord = F.Id("lambdaPrime");
        Formula stateReadout = F.Id("s");

        Formula historyData = Seq(
            Apply(endpoint, first), Sp, Eq, Sp, state, Sp, Land, Sp,
            Apply(endpoint, second), Sp, Eq, Sp, state, Sp, Land, Sp,
            Apply(recordImage, first), Sp, Eq, Sp, firstRecord, Sp, Land, Sp,
            Apply(recordImage, second), Sp, Eq, Sp, secondRecord, Sp, Land, Sp,
            firstRecord, Sp, Neq, Sp, secondRecord);
        Formula stateClause = Seq(
            Forall, Sp, stateReadout, Colon, Sp,
            Arrow(stateType, stateOutputType), Comma, Sp,
            Apply(stateReadout, Apply(endpoint, first)), Sp, Eq, Sp,
            Apply(stateReadout, Apply(endpoint, second)));
        Formula composedRecordReadout = Seq(recordReadout, Sp, Circ, Sp, recordImage);
        Formula recordClause = Seq(
            Neg, Sp, Call("ker", composedRecordReadout, first, second),
            Sp, Iff, Sp,
            Apply(recordReadout, firstRecord), Sp, Neq, Sp,
            Apply(recordReadout, secondRecord));

        return Disp(Seq(
            Forall, Sp,
            stateType, Comma, Sp, recordType, Comma, Sp, readingType, Comma, Sp,
            stateOutputType, Comma, Sp, recordOutputType, Comma, Sp, historyType,
            Colon, Sp, type, Comma, Esc,
            recordOps, Colon, Sp, recordOpsType, Comma, Esc,
            observer, Colon, Sp, observerType, Comma, Esc,
            historyOps, Colon, Sp, historyOpsType, Comma, Esc,
            first, Comma, Sp, second, Colon, Sp, historyType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            firstRecord, Comma, Sp, secondRecord, Colon, Sp, recordType, Comma, Esc,
            Open, historyData, Close, Sp, Rightarrow, Esc,
            Open, stateClause, Close, Sp, Land, Esc,
            Open, recordClause, Close, Dot));
    }
}
