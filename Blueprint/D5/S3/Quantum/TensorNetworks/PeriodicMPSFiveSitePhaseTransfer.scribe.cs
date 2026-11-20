using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSitePhaseTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSitePhaseTransfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer to full amplitudes and the adjacent marginal",
        H("Transfer to full amplitudes and the adjacent marginal"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitephasetransfer-result"),
            DeclarationHandle.Create(Module + ".transfer_rawTwo_unitPhase"),
            H("Transfer to full amplitudes and the adjacent marginal"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Singleton fibers on an open dense compact locus imply an open dense phase-recovery statement for the full unit-mass amplitudes."))),
            DescribeRole.Theorem))));
}
