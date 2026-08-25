using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class PassiveAdaptiveTranscriptUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound."
            + "passive_adaptive_transcript_upper_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every deterministic adaptive transcript using a passive experiment family "
            + "factors through the complete joint experiment readout.",
        H("Passive Adaptive Transcript Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("passive-adaptive-transcripts-factor-through-all-experiments"),
            DeclarationHandle.Create(Declaration),
            H("Every passive adaptive transcript factors through all experiment answers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A passive protocol is a finite dependent decision tree. At each query "
                        + "node, the answer selects the continuation, so later experiments "
                        + "may depend on the transcript already observed.")),
                Paragraph(Text(
                    "The operational evaluator reads each selected channel from the state. "
                        + "A separate replay evaluator follows the same tree from the complete "
                        + "dependent tuple of all experiment answers. Induction on the protocol "
                        + "identifies the two transcripts and supplies the factor map."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula experimentType = F.Id("U");
        Formula stateType = F.Id("X");
        Formula response = F.Id("R");
        Formula experiment = F.Id("u");
        Formula readout = F.Id("q");
        Formula protocol = F.Id("pi");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula responseAt = new Formula.Subscript(response, experiment);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, experimentType, Comma, Sp, stateType, Colon, Sp, type,
                Comma, Sp, response, Colon, Sp, experimentType, Sp, To, Sp, type,
                Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, experiment, Colon, Sp,
                experimentType, Comma, Sp, stateType, Sp, To, Sp, responseAt,
                Comma),
            Seq(
                protocol, Colon, Sp, Call("PassiveProtocol", experimentType, response),
                Comma, Sp,
                Call(
                    "Refines",
                    Call("runPassiveProtocol", readout, protocol),
                    Call("jointReadout", readout)),
                Dot),
        ]));
    }
}
