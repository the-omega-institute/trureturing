using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSCommonSpectralAllLengthsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralAllLengths";
    private const string Title = "The literal determinant at every suffix length";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpscommonspectralalllengths-literaljacobian-det-ne-zero"),
                DeclarationHandle.Create(Module + ".literalJacobian_det_ne_zero"),
                H("The literal determinant at every suffix length"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural suffix length at least five the literal trace-word Jacobian has nonzero determinant."))),
                DescribeRole.Theorem))));
}
