using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSCommonSpectralDeterminantDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralDeterminant";
    private const string Title = "The determinant at every suffix length";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpscommonspectraldeterminant-det-l-at-length-ge-five-ne-zero"),
                DeclarationHandle.Create(Module + ".det_L_at_length_ge_five_ne_zero"),
                H("The determinant at every suffix length"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed-form witness determinant is nonzero for every integer suffix length at least five."))),
                DescribeRole.Theorem))));
}
