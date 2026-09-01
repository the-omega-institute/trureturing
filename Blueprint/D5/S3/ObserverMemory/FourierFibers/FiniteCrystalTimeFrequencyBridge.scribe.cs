using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class FiniteCrystalTimeFrequencyBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separated finite crystal spectrum is reconstructed from an equally long scalar time window.",
        H("Finite Crystal Time-Frequency Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-crystal-time-window-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective"),
                H("Separated modes are recovered from time samples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many distinct modal multipliers, the first matching number of scalar time samples uniquely recovers all modal amplitudes.")),
                    Paragraph(Text(
                        "This is a finite diagonal spectral realization of Vandermonde tomography. It does not construct an infinite Bloch bundle or identify the sampling index with physical time."))),
                DescribeRole.Theorem))));
}
