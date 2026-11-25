using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrame";
    private const string Title = "Moving frames for the periodic mixed transfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframe"),
                DeclarationHandle.Create(Module + ".mixedRaw_movingFrame_jet"),
                H("Moving-frame derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-site mixed readout transforms by the value of the pair frame. Its first-order term acquires the physical tangent of the frame, which is subtracted to recover the transported derivative."))),
                DescribeRole.Theorem))));
}
