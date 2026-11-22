using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpectralCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralCoefficients";
    private const string Title = "The trace-aligned transfer coefficient guard";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-coefficients-guard-formula"),
                DeclarationHandle.Create(Module + ".ambientGuard_formula"),
                H("The ambient transfer guard"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the independent determinant variables d, db, e and eb and the mixed trace k, the ambient guard is (d db) k (c − b²), where b and c are the second and third entries of the transfer coefficient tuple."))),
                DescribeRole.Theorem))));
}
