using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class RootTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace square root under block pinching",
        H("Trace square root under block pinching"),
        Blocks(Describe.Lean(
            DescribeId.Create("trace-sqrt-le-of-two-blocks"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/RootTrace.trace_sqrt_le_of_two_blocks"),
            H("Trace square root under block pinching"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Averaging a positive matrix with its conjugate by the sign unitary eliminates the off-block entries. Trace-square-root concavity and unitary invariance control the trace."))),
            DescribeRole.Theorem))));
}
