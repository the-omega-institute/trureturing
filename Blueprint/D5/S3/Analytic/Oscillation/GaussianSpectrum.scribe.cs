using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class GaussianSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/GaussianSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian mass and continuous cosine sums of positive ordinates.",
        H("Gaussian spectral sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectrum-countable"),
                DeclarationHandle.Create(Prefix + "spectrum_countable"),
                H("Countability of the spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index type of a locally finite positive spectrum is countable: the finite sets of ordinates at most each natural number exhaust it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("count-bound"),
                DeclarationHandle.Create(Prefix + "count_bound"),
                H("Logarithmic counting growth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the multiplicity-weighted count divided by T log T tends to 1/(2 pi), "
                    + "there is C>0 such that N(T) is at most C T log(2+T) for every T at least "
                    + "one. Monotonicity controls bounded cutoffs, and the limit controls the "
                    + "remaining cutoffs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-square-summable"),
                DeclarationHandle.Create(Prefix + "inverse_square_summable"),
                H("Summability of inverse squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally finite positive spectrum with the counting asymptotic, the sum "
                    + "of multiplicity divided by the square of each ordinate converges. The finite "
                    + "cutoff at four and the convergent inverse-square tail cover the entire "
                    + "spectrum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-coefficients-summable"),
                DeclarationHandle.Create(Prefix + "gaussian_coefficients_summable"),
                H("Summable Gaussian coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every positive scale M, the multiplicity-weighted Gaussian coefficients "
                    + "are summable. The inequality exp(-x) <= 1/x for x>0 bounds each coefficient "
                    + "by 2 M squared times the multiplicity divided by the ordinate squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-cos-summable"),
                DeclarationHandle.Create(Prefix + "gaussianCos_summable"),
                H("Absolute convergence of the cosine series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive M and real y, the Gaussian-weighted cosine series "
                    + "converges absolutely. The absolute value of each cosine is at most one, so "
                    + "the Gaussian coefficients form a summable majorant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-cos-continuous"),
                DeclarationHandle.Create(Prefix + "gaussianCos_continuous"),
                H("Continuity of the cosine sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive M, the Gaussian spectral cosine sum is a continuous "
                    + "function of y. Each summand is continuous and its absolute value has a "
                    + "summable bound independent of y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-gaussian-cos-le"),
                DeclarationHandle.Create(Prefix + "abs_gaussianCos_le"),
                H("Uniform bound by Gaussian mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive M and every real y, the absolute value of the Gaussian "
                    + "cosine sum is at most the total Gaussian mass at scale M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-mass-bound"),
                DeclarationHandle.Create(Prefix + "gaussian_mass_bound"),
                H("Gaussian spectral mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is C>0 such that the total multiplicity-weighted Gaussian mass is at "
                    + "most C M log(2+M) for every M at least one. Split at ordinate 4M, use the "
                    + "counting bound on the finite part, and apply the inverse-square tail "
                    + "estimate to the remaining Gaussian coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transition-mass-bound"),
                DeclarationHandle.Create(Prefix + "transition_mass_bound"),
                H("Transition-band mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every unit window starting at t>=0 has multiplicity at most A log(t+3), "
                    + "there is C>0 such that N(M+Delta)-N(M) is at most C Delta log(2+M) whenever "
                    + "1<=Delta<=M. Cover the interval by the ceiling of Delta unit windows and "
                    + "telescope their counts."))),
                DescribeRole.Theorem))));
}
