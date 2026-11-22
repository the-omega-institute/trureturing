using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalClearedHermiteDocument : IScribeDocumentDefinition
{
    private const string Title = "Cleared Hermite coefficients";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalclearedhermite-clearedhermite-eq-clear-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalClearedHermite.clearedHermite_eq_clear_mul"),
                H("Clearing the split Hermite interpolant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A product of nodal gaps clears the value and slope cardinals in their specified order."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalclearedhermite-clearedhermite-coeff-totaldegree"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalClearedHermite.clearedHermite_coeff_totalDegree"),
                H("Spectral degree of the eight coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding the cleared interpolation formula in the power variable bounds each coefficient independently."))),
                DescribeRole.Theorem))));
}
