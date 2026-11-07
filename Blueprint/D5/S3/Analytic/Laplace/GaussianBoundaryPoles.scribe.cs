using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class GaussianBoundaryPolesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/GaussianBoundaryPoles.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute Gaussian integration of a paired spectral pole expansion.",
        H("Gaussian integration of paired poles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pole-gaussian-tsum-integrable"),
                DeclarationHandle.Create(Prefix + "pole_gaussian_tsum_integrable"),
                H("Absolute integrability of the full series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the weighted ordinate count has the specified logarithmic "
                    + "asymptotic, the full paired-pole series multiplied by the Gaussian "
                    + "factor is integrable on Re(s)=3/4. The sum of m/gamma squared "
                    + "is finite and supplies a single integrable quadratic majorant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectrum-cut-tendsto"),
                DeclarationHandle.Create(Prefix + "spectrum_cut_tendsto"),
                H("Exhaustion by ordinate cutoffs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "As the real cutoff tends to infinity, the finite set of ordinates "
                    + "below that cutoff tends to the filter of all finite subsets. "
                    + "The cutoffs are increasing and every ordinate belongs to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-gaussian-cutoff-tendsto"),
                DeclarationHandle.Create(Prefix + "pole_gaussian_cutoff_tendsto"),
                H("Convergence of finite-cutoff integrals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integrals of the Gaussian-weighted finite paired-pole sums "
                    + "converge, as the ordinate cutoff tends to infinity, to the "
                    + "integral of the full paired-pole series. Absolute summability "
                    + "of the integrated norms permits passage along the finite cutoffs."))),
                DescribeRole.Theorem))));
}
