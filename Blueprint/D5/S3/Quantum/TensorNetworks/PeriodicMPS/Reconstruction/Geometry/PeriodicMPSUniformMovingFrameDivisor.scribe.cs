using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameDivisorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameDivisor";
    private const string Title = "Unnormalized paired section in the native frame";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframedivisor"),
                DeclarationHandle.Create(Module + ".native_section_unnormalized_jet"),
                H("Transport of the full raw first jet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The balancing equation lifts to inverse frames over the dual numbers. The resulting raw section tangent is expressed through native critical columns at the balanced Cartesian point."))),
                DescribeRole.Theorem))));
}
