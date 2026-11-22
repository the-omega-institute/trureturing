using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTraceAmplitudeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceAmplitude";
    private const string Title = "Weighted scaling of periodic trace-word amplitudes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtraceamplitude-result"),
            DeclarationHandle.Create(Module + ".amplitudeOfLength_scale"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At every length n, multiplying both trace coordinates by z and the three quadratic invariants by z² multiplies the whole trace-word tensor by zⁿ. The coefficient polynomial uses the same two-by-two trace algebra as the seven-site construction."))),
            DescribeRole.Theorem))));
}
