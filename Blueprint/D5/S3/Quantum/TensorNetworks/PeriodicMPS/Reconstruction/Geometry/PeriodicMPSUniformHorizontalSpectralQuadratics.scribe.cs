using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalSpectralQuadraticsDocument : IScribeDocumentDefinition
{
    private const string Title = "Spectral degrees of the determinant square rules";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalspectralquadratics-chart-quadratic-totaldegrees"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalSpectralQuadratics.chart_quadratic_totalDegrees"),
                H("Bounds for the two determinant radicals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The elementary spectral invariants give bounds six and twelve for the two radical squares, using either parameter convention for the second pair."))),
                DescribeRole.Theorem))));
}
