using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameColumnsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameColumns";
    private const string Title = "Native columns on the paired section";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframecolumns"),
                DeclarationHandle.Create(Module + ".native_section_rotation_column"),
                H("Transport of rotation columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After normalization and balance, the Pauli readout of each physical rotation tangent lies in the column span of the evaluated native critical matrix."))),
                DescribeRole.Theorem))));
}
