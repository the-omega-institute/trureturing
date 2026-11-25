using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameRowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRows";
    private const string Title = "Swap-symmetric two-site readout";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframerows"),
                DeclarationHandle.Create(Module + ".unobserve_pauliRead"),
                H("Reconstruction from ten Pauli rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a swap-symmetric matrix, reconstruction from the ten observed Pauli coordinates gives the original matrix."))),
                DescribeRole.Theorem))));
}
