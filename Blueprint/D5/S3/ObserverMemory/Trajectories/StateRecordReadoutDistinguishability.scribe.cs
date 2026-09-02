using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class StateRecordReadoutDistinguishabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal endpoints collapse under state readouts; record separation is exactly output inequality.",
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
                        "Let two histories have the same endpoint x and respective record "
                            + "images lambda and lambdaPrime, with the record images distinct. "
                            + "The endpoint and record-image maps use the repository's canonical "
                            + "generic Concept readout carrier.")),
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
        Formula historyType = F.Id("Gamma");
        Formula stateType = F.Id("X");
        Formula recordType = new Formula.Subscript(F.Id("Lambda"), D(1));
        Formula stateOutputType = F.Id("Y");
        Formula recordOutputType = new Formula.Subscript(F.Id("Y"), D(2));
        Formula endpoint = F.Id("e");
        Formula recordImage = F.Id("r");
        Formula recordReadout = new Formula.Subscript(F.Id("q"), D(2));
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
            historyType, Comma, Sp, stateType, Comma, Sp, recordType, Comma, Sp,
            stateOutputType, Comma, Sp, recordOutputType,
            Colon, Sp, type, Comma, Esc,
            endpoint, Colon, Sp, Arrow(historyType, stateType), Comma, Sp,
            recordImage, Colon, Sp, Arrow(historyType, recordType), Comma, Sp,
            recordReadout, Colon, Sp, Arrow(recordType, recordOutputType), Comma, Esc,
            first, Comma, Sp, second, Colon, Sp, historyType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            firstRecord, Comma, Sp, secondRecord, Colon, Sp, recordType, Comma, Esc,
            Open, historyData, Close, Sp, Rightarrow, Esc,
            Open, stateClause, Close, Sp, Land, Esc,
            Open, recordClause, Close, Dot));
    }
}
