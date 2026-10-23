using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBetaShape;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict coefficient signs for real shifts of the first incomplete beta parameter.",
        H("Coefficient convolution and shape imbalance"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-convolution-decrease"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictAnti_imbalance"),
                H("Strict decrease with imbalance above one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let m be positive, n natural, and b greater than one. The sum over k from zero through n of c(k,m+d,b)c(n-k,m-d,b) strictly decreases as d ranges from zero, included, to m, excluded. The affine beta-mixture representation gives a common positive factor at fixed 2m. Its remaining factor is the beta mean of the continuous symmetric kernel H, which strictly increases toward its midpoint. The existing beta-mean comparison therefore gives strict decrease with the imbalance d."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-convolution-increase"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Result.convolution_strictMono_imbalance"),
                H("Strict increase with imbalance below one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When b lies strictly between zero and one, the same convolution strictly increases with d. The function -H is continuous, symmetric, and strictly increasing toward the midpoint, so it satisfies the beta-mean comparison hypotheses. Linearity of the integral reverses the resulting inequality for H."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-coefficient-sign"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Result.result"),
                H("The strict coefficient signs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all positive real a, b, alpha and beta, and every natural n, the coefficient psi(n) is strictly negative when b is less than one and strictly positive when b is greater than one. Here c(j,t,b) is Gamma(t+b+j) divided by Gamma(b)Gamma(t+j+1), and psi(n) sums c(k,a+alpha,b)c(n-k,a+beta,b) minus c(k,a,b)c(n-k,a+alpha+beta,b) over k from zero through n. The coefficients are independent of x, so these signs give strict coefficient-wise Wright log-convexity below one and strict coefficient-wise Wright log-concavity above one for the normalized incomplete beta series.")),
                    Paragraph(Text("Both parameter pairs have mean m=a+(alpha+beta)/2. Their nonnegative half-differences are |alpha-beta|/2 and (alpha+beta)/2. Positivity of both shifts makes the first strictly smaller. The convolution comparison, together with commutativity of the finite convolution, gives the two signs without restricting either shift to integers."))),
                DescribeRole.Theorem))));
}
