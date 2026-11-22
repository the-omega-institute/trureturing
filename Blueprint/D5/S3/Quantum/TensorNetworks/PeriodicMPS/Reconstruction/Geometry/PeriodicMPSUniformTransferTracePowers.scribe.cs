using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformTransferTracePowersDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferTracePowers";
    private const string Title = "Periodic transfer trace powers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformtransfertracepowers-mixedtransfer-trace-powers"),
                DeclarationHandle.Create(Module + ".mixedTransfer_trace_powers"),
                H("Periodic transfer trace powers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace of a power of the mixed transfer matrix agrees with the trace-word contraction."))),
                DescribeRole.Theorem))));
}
