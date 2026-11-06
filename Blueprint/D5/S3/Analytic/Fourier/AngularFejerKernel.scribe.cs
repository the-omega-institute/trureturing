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
