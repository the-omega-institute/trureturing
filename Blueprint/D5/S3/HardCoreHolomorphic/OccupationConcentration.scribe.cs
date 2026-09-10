using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class OccupationConcentrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform complex response bounds control actual discrete Gibbs fluctuations.",
        H("OccupationConcentration"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-density-mean-square"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.densityMeanSquare"),
                H("densityMeanSquare"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mean-square fluctuation of the actual occupation density. The weights are point masses of the existing Gibbs PMF. Empty domains are excluded whenever this expression is interpreted as a density."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-density-mean-square-eq"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.density_mean_square_eq"),
                H("density mean square eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rescaling the actual centered moment gives variance divided by volume squared. No independent-site assumption is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-grid-density-mean-square-bound"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_mean_square_bound"),
                H("grid density mean square bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is mean-square concentrated around its own finite-volume mean, with a volume-independent coefficient. This makes no assertion that those means have a common infinite-volume limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-density-deviation-mass"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.densityDeviationMass"),
                H("densityDeviationMass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual Gibbs event probability, written as the finite sum of point masses. It is not a probability assigned to complex normalized weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-density-deviation-mass-bounds"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_mass_bounds"),
                H("density deviation mass bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The event expression is a number between zero and one, by positivity and normalization of the actual finite probability law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-density-deviation-le-second-moment"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.density_deviation_le_second_moment"),
                H("density deviation le second moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite Chebyshev estimate on this exact Gibbs sample space. The event threshold is positive; the density denominator is not used for division in this proof, so the algebraic inequality also covers the empty domain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-variance-occupationconcentration-grid-density-deviation-bound"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationConcentration.grid_density_deviation_bound"),
                H("grid density deviation bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite-size concentration around the actual finite-volume mean. The constant comes from the proved analytic variance bound, not a supplied concentration hypothesis. It becomes O(1/volume) for any fixed threshold."))), DescribeRole.Theorem))));
}
