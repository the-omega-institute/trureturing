using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTraceNormalLimitsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalLimits";
    private const string Title = "Normal amplitudes over proportional trace-word zeros";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracenormallimits-result"),
            DeclarationHandle.Create(Module + ".limit_at_proportional"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At each period n ≥ 2, a sequence in the trace-one chart with eventually nonzero amplitudes may approach a proportional base point. If its projectors converge, the limit is the projector of a nonzero normal amplitude at that point. The proof normalizes the normal coordinates before taking a subsequence."))),
            DescribeRole.Theorem))));
}
