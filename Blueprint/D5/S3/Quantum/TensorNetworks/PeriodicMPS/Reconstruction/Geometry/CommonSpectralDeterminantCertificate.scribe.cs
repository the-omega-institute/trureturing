using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class CommonSpectralDeterminantCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/CommonSpectralDeterminantCertificate";
    private const string Title = "The common witness polynomial determinant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("commonspectraldeterminantcertificate-det-input"),
                DeclarationHandle.Create(Module + ".det_input"),
                H("The common witness polynomial determinant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Polynomial elimination calculates the determinant of the certificate matrix."))),
                DescribeRole.Theorem))));
}
