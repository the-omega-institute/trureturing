using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameNativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameNative";
    private const string Title = "Native Pauli readout of moving-frame jets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframenative"),
                DeclarationHandle.Create(Module + ".native_movingFrame_comparison"),
                H("Native evaluation of a transported jet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An invertible dual-number frame with aligned traces and equal mixed traces expresses the observed first-order readout in the slice and physical-rotation columns of the evaluated native matrix."))),
                DescribeRole.Theorem))));
}
