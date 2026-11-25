using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalNativeCofactorDegreeDocument : IScribeDocumentDefinition
{
    private const string Title = "Native cofactor degrees in the radical chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalnativecofactordegree-clearednativeminor-degreele"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalNativeCofactorDegree.clearedNativeMinor_degreeLE"),
                H("The nine-column determinant has weighted degree at most 801"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the seven-degree column budget for each of the five derivative columns and the eight-degree budget for the four remaining columns."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalnativecofactordegree-nativecrossedscalar-shiftedcoeff-totaldegree-le"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalNativeCofactorDegree.nativeCrossedScalar_shiftedCoeff_totalDegree_le"),
                H("Both Laurent projections preserve the bound 1602"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product with the second-radical sign reversal doubles the weighted bound. Clearing Laurent powers and taking the scalar coefficient preserve the spectral bound."))),
                DescribeRole.Theorem))));
}
