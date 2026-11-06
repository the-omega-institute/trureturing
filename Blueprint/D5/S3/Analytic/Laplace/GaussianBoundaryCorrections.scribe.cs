using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class GaussianBoundaryCorrectionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/GaussianBoundaryCorrections.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflected Gaussian corrections for positive-ray cosine integrals.",
        H("Gaussian half-line corrections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-cos-halfline"),
                DeclarationHandle.Create(Prefix + "gaussian_cos_halfline"),
                H("Cosine inversion on a half-line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive Gaussian scale, the integral of cos(gamma u) "
                    + "against q_M(y-u) on the nonnegative half-line equals "
                    + "exp(-gamma squared divided by twice M squared) cos(gamma y), "
                    + "less the integral of cos(gamma v) q_M(y+v) over v at least zero. "
                    + "Split the full Gaussian cosine convolution at zero and reflect "
                    + "the negative half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-corrections-summable"),
                DeclarationHandle.Create(Prefix + "gaussian_corrections_summable"),
                H("Absolute summability of the corrections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the multiplicity count of a locally finite positive "
                    + "spectrum is asymptotic to T log(T) divided by twice pi. "
                    + "For M and y at least one, the reflected Gaussian corrections, "
                    + "multiplied by their spectral multiplicities, form an absolutely "
                    + "summable family. Two integrations by parts bound each term "
                    + "by a common factor times multiplicity divided by gamma squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-corrections-bound"),
                DeclarationHandle.Create(Prefix + "gaussian_corrections_bound"),
                H("An exponentially small correction sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same spectral counting assumption, there is a "
                    + "positive constant C, independent of M and y, such that for "
                    + "M and y at least one the absolute value of the summed "
                    + "multiplicity-weighted reflected corrections is at most "
                    + "C M cubed exp(-y/6). The inverse-square spectral sum is finite, "
                    + "and the Gaussian factor obeys M squared times y times q_M(y) "
                    + "at most three M cubed exp(-y/6) divided by sqrt(2 pi)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-halfline-summable"),
                DeclarationHandle.Create(Prefix + "gaussian_halfline_summable"),
                H("Summing the positive-ray cosine integrals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For M and y at least one, the integrals of the spectral "
                    + "cosines against q_M(y-u) on the nonnegative half-line, "
                    + "with multiplicities included, form a summable family. "
                    + "They are the differences between the summable Gaussian "
                    + "cosine coefficients and the summable reflected corrections."))),
                DescribeRole.Theorem))));
}
