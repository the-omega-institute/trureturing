using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformTransferSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSpectrum";
    private const string Title = "The trace-aligned transfer spectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformtransferspectrum-ketfirst-charpoly-trace-aligned"),
                DeclarationHandle.Create(Module + ".ketFirst_charpoly_trace_aligned"),
                H("The trace-aligned transfer spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace-aligned coordinates give the characteristic quartic of the ket-first transfer matrix."))),
                DescribeRole.Theorem))));
}
