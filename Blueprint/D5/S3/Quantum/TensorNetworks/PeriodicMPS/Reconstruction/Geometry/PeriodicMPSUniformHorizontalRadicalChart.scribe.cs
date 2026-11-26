using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalRadicalChartDocument : IScribeDocumentDefinition
{
    private const string Title = "Component degrees in the two radical charts";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalradicalchart-radicaldegreele-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart.mul"),
                H("Multiplication adds weighted degrees"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four coefficient slots carry weights zero, three, six, and nine. Reducing either squared radical preserves the sum of the weighted bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalradicalchart-radicalcoordinatesu-degreele"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart.radicalCoordinatesU_degreeLE"),
                H("Bounds at fixed k"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered determinant coordinates retain their component bounds with the inverse of k in the second pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalradicalchart-radicalcoordinatesk-degreele"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart.radicalCoordinatesK_degreeLE"),
                H("Bounds at fixed U"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scaled second pair and the first determinant pair satisfy the same component bounds in the other projection."))),
                DescribeRole.Theorem))));
}
