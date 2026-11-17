using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class AngularFejerKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/AngularFejerKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Angular Fejer kernels, their Fourier transforms, tail bounds, and logarithmic averages.",
        H("Angular Fejer kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cosine-convolution"),
                DeclarationHandle.Create(Prefix + "cosine_convolution"),
                H("Convolution with a cosine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If g is integrable and its angular Fourier transform is the real-valued function w, then convolution of g with cos(gamma u) equals w(gamma) cos(gamma y). Translation of the complex exponential integral gives the identity after taking real parts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phi-continuous"),
                DeclarationHandle.Create(Prefix + "phi_continuous"),
                H("Continuity of the tent weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Fejer tent Fourier weight is continuous for every real bandwidth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phi-eq-zero"),
                DeclarationHandle.Create(Prefix + "phi_eq_zero"),
                H("Vanishing outside the bandwidth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive b, the Fejer tent weight vanishes at every t with absolute value at least b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-cap"),
                DeclarationHandle.Create(Prefix + "K_cap"),
                H("The height of the Fejer kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive b, K(b,v) is at most b/(2*pi) at every real v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-continuous"),
                DeclarationHandle.Create(Prefix + "K_continuous"),
                H("Continuity of the Fejer kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The angular Fejer kernel is continuous for every real bandwidth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("notched-kernel-continuous"),
                DeclarationHandle.Create(Prefix + "H_continuous"),
                H("Continuity of the notched kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The notched Fejer kernel is continuous for every real bandwidth and notch location."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("angular-fourier"),
                DeclarationHandle.Create(Prefix + "aft_fourier"),
                H("Angular and cyclic Fourier conventions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The angular Fourier transform at t equals the cyclic Fourier transform at t/(2*pi)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-ell-nonneg"),
                DeclarationHandle.Create(Prefix + "log_ell_nonneg"),
                H("Nonnegativity of the logarithmic envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative u, log(exp(1)+u) is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fejer-law"),
                DeclarationHandle.Create(Prefix + "fejer_law"),
                H("The angular Fejer kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive bandwidth b, the angular Fejer kernel K(b,v) is nonnegative and "
                    + "integrable with total mass one. Its angular Fourier transform is the triangular function "
                    + "max(0,1-abs(t)/b). For every positive y, its integral over v at least y is at most "
                    + "2/(pi*b*y)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("notched-fejer-law"),
                DeclarationHandle.Create(Prefix + "notched_fejer_law"),
                H("The notched Fejer kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive b and U greater than 2*b, the notched kernel H(b,U,v)=K(b,v)*(1-cos(U*v)) lies "
                    + "between zero and 2*K(b,v), is integrable, and has total mass one. Its angular Fourier "
                    + "transform is phi(b,t)-phi(b,t-U)/2-phi(b,t+U)/2. Its integral over v at least a positive y "
                    + "is at most 4/(pi*b*y)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fejer-log-average"),
                DeclarationHandle.Create(Prefix + "fejer_log_average"),
                H("Uniform logarithmic averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a nonnegative constant C independent of M and y such that, for M and y at least "
                    + "one, K(M,y-u)*log(exp(1)+u) is integrable on the nonnegative half-line and its integral is "
                    + "at most log(exp(1)+y)+C. The bound follows from the finite logarithmic moment of K(1,.) and "
                    + "dilation of the kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("notched-log-average"),
                DeclarationHandle.Create(Prefix + "notched_log_average"),
                H("Logarithmic averages for notched kernels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive b, there is a nonnegative constant depending only on b such that, whenever "
                    + "U is greater than 2*b and y is at least one, H(b,U,y-u)*log(exp(1)+u) is integrable on the "
                    + "nonnegative half-line and its integral is at most log(exp(1)+y) plus that constant. "
                    + "Positivity and unit mass give coefficient one for the logarithm; comparison with 2*K(b,.) "
                    + "bounds the remaining logarithmic moment uniformly in U."))),
                DescribeRole.Theorem))));
}
