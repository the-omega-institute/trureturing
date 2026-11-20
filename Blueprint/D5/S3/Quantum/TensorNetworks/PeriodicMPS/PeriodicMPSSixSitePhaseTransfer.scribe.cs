using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSitePhaseTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent from compact six-site fibers to literal marginal recovery",
        H("Descent from compact six-site fibers to literal marginal recovery"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitephasetransfer-transfer-rawtwo-unitphase"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSitePhaseTransfer.transfer_rawTwo_unitPhase"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Compact singleton observation fibers give an open dense unit-mass amplitude locus by continuous local phase sections."))), DescribeRole.Theorem))));
}
