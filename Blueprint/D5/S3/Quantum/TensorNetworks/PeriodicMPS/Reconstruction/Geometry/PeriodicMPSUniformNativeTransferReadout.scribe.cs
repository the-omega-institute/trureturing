using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformNativeTransferReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformNativeTransferReadout";
    private const string Title = "Transfer powers for the actual two-site Gram matrix";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformnativetransferreadout"),
                DeclarationHandle.Create(Module + ".pairGram_traceWord_eq_mixedRaw"),
                H("Mixed transfer gives the two-site Gram matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At length 2 + m the unnormalized adjacent-pair Gram matrix of the trace-word amplitude equals the mixed-transfer readout of the core and its conjugate."))),
                DescribeRole.Theorem))));
}
