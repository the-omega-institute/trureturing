using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class CompoundPoissonEdgeworthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent Poisson jumps with irrational ratio satisfy a uniform first Edgeworth expansion, a fixed-width local limit, and uniform atom decay.",
        H("Real-time Edgeworth expansion for two Poisson jumps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-signed-smoothing"),
                DeclarationHandle.Create(Prefix + "generic_finite_smoothing"),
                H("Finite-frequency smoothing for a signed density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let P be any probability measure on the real line, and let q be an integrable real comparison density bounded in absolute value by A. Assume its lower-half-line integral is Lipschitz with constant A. There is a universal positive H such that, for every positive bandwidth on whose frequency interval the weighted Fourier difference is integrable, the distribution-function error is bounded by twice that Fourier integral plus 4AH divided by the bandwidth.")),
                    Paragraph(Text("Convolution with a squared-sinc probability density cuts off Fourier frequencies. Monotonicity of the actual distribution function and the Lipschitz property of the signed comparison absorb the remaining tail discrepancy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-frequency-poisson-error"),
                DeclarationHandle.Create(Prefix + "low_frequency_integral_vanishes"),
                H("A Gaussian envelope on a growing frequency interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write V for p times a squared plus q times b squared, and use the raw cubic and quartic jump moments. On a sufficiently small fixed raw-frequency interval, the cubic and quartic exponent terms are bounded by V times u squared divided by four, leaving Gaussian decay exp(-V u squared / 4).")),
                    Paragraph(Text("After rescaling by square-root time w, the error divided by frequency is bounded by a Gaussian times a polynomial of degrees three, five, and seven, divided by w squared. This integrable envelope makes w times the low-frequency integral tend to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-cutoff-poisson-error"),
                DeclarationHandle.Create(Prefix + "symmetric_cutoff_vanishes"),
                H("The full moving-cutoff Fourier error vanishes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Assume p and q are positive, b is nonzero, and a divided by b is irrational. For every fixed positive C, w times the characteristic-function error integral over the symmetric interval from minus Cw to Cw tends to zero. The comparison uses variance V and the raw third jump moment.")),
                    Paragraph(Text("Irrationality prevents both cosine terms from attaining one at a nonzero frequency. Compactness therefore gives a positive damping gap on each fixed annulus. The low-frequency Gaussian estimate, this annular gap, and an integrable Gaussian correction tail control the whole interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compound-poisson-edgeworth-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Uniform Edgeworth expansion, local limits, and atom decay"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take independent Poisson counts with means lambda times p and lambda times q. The weighted sum has mean lambda times (pa+qb) and variance lambda times (p a squared+q b squared). Standardize by that exact mean and variance. The correction coefficient uses p a cubed+q b cubed, the raw third jump moment.")),
                    Paragraph(Text("For every positive error tolerance, all sufficiently large real lambda satisfy the first Edgeworth estimate uniformly over every real threshold. Choose the raw-frequency cutoff first and then let square-root time grow; finite signed smoothing and the moving-cutoff estimate give the limit.")),
                    Paragraph(Text("For every fixed positive width h, the probability that the unstandardized weighted sum lies in (y,y+h], multiplied by square-root lambda, converges uniformly in y to h divided by the square root of V times the standard Gaussian density at the standardized left endpoint. Uniform continuity of the Gaussian density and its correction controls the difference of the two distribution functions.")),
                    Paragraph(Text("The mass at every standardized score, multiplied by square-root lambda, tends uniformly to zero. The comparison distribution function is continuous, so its uniform error bounds the jump of the actual distribution function. All three conclusions use arbitrary fixed positive rates and arbitrary real jump sizes subject to the nonzero denominator and irrational-ratio hypotheses."))),
                DescribeRole.Theorem))));
}
