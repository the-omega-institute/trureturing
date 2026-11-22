using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralRowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRows";
    private const string Title = "Detection by the observed rows";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralrows-observedpauligram-injective-on-differential"),
                DeclarationHandle.Create(Module + ".observedPauliGram_injective_on_differential"),
                H("Detection by the observed rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exchange symmetry of the Gram derivative makes the selected observed Pauli rows injective on its image."))),
                DescribeRole.Theorem))));
}
