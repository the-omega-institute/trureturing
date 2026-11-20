using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteTraceChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteTraceChart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace-pencil frames for five-site amplitudes",
        H("Trace-pencil frames for five-site amplitudes"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitetracechart-result"),
            DeclarationHandle.Create(Module + ".frame_trace_coordinates"),
            H("Trace-pencil frames for five-site amplitudes"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The frame polynomial recovers the five-site trace coordinates from the trace direction and pencil entries."))),
            DescribeRole.Theorem))));
}
