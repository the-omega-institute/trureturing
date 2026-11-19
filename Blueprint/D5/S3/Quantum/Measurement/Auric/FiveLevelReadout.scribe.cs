using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class FiveLevelReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Purification and effect lower bound",
        H("Purification and effect lower bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-flag-score-le-trace-error"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/FiveLevelReadout.two_flag_score_le_trace_error"),
            H("Purification and effect lower bound"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A diagonal purification and an orthonormal two-flag output frame turn the difference of Choi scores into the expectation of an effect, bounding the unhalved trace error."))),
            DescribeRole.Theorem))));
}
