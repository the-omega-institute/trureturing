using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FirstOrderInterfaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every continuous real weight on [1,2], the weighted first normalized moment tends to zero uniformly over s in [0,1], under the variance asymptotic on a band containing theta. The second absolute moment bound controls the approximation error, and uniform interval cancellation supplies the step-weight limit.",
        H("Uniform first moments with continuous weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-weight-regular"),
                DeclarationHandle.Create(Prefix + "logarithmic_weight_regular"),
                H("Reciprocal power-logarithmic weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative p and q, the reciprocal of x^p log(x)^q is continuously differentiable, nonnegative and decreasing on x>1. Increasing the position increases both positive factors of its denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-interval-cancellation"),
                DeclarationHandle.Create(Prefix + "first_interval_cancellation"),
                H("Uniform first primitive cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally bounded Borel function whose cumulative variance has the stated uniform asymptotic on an exponent band containing theta, the integral of D_(s*x^theta)(x) on any subinterval of [X,2X], divided by X*sqrt(X^theta*log(X)), tends to zero uniformly over s in [0,1] and both endpoints. An intermediate exponent nu between theta and the upper band endpoint gives two negative powers after normalization of the moving primitive estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("logarithmic-weight-cancellation"),
                DeclarationHandle.Create(Prefix + "logarithmic_weight_cancellation"),
                H("Cancellation with a decreasing logarithmic weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integrable family with uniform interval cancellation relative to X^p log(X)^q, where p and q are nonnegative, multiplication by the reciprocal power-logarithmic weight gives uniform unscaled interval cancellation. Integration by parts bounds each weighted integral by twice the primitive bound times the weight at X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-weighted-interval-cancellation"),
                DeclarationHandle.Create(Prefix + "first_weighted_interval_cancellation"),
                H("Normalized first moments on subintervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the variance band asymptotic, the integral of B_theta(s,x)/x tends to zero uniformly over s in [0,1] and all subintervals of [X,2X]. This is the first moving increment multiplied by x^(-1-theta/2) log(x)^(-1/2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-b-power-integrable"),
                DeclarationHandle.Create(Prefix + "dyadicB_power_integrable"),
                H("Integrability of normalized increment powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every natural power of the normalized moving increment is integrable under logarithmic dyadic probability when X>1 and theta is nonnegative. The same power divided by position is interval integrable on [X,2X]. Local boundedness supplies integrable raw powers and the normalizing factor is continuous on this interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-dyadic-weight-lifting"),
                DeclarationHandle.Create(Prefix + "continuous_dyadic_weight_lifting"),
                H("Continuous dyadic weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An interval integrable family with bounded absolute logarithmic mass and uniform cancellation on all dyadic subintervals has vanishing integrals against every continuous function of x/X under dyadic probability. The change of variables x=X*u reduces this to continuous weight approximation on [1,2]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-moment-uniform"),
                DeclarationHandle.Create(Prefix + "first_moment_uniform"),
                H("Uniform first moments with continuous weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every continuous real weight on [1,2], the weighted first normalized moment tends to zero uniformly over s in [0,1], under the variance asymptotic on a band containing theta. The second absolute moment bound controls the approximation error, and uniform interval cancellation supplies the step-weight limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-moment-interface"),
                DeclarationHandle.Create(Prefix + "first_moment_interface"),
                H("The first-moment interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A locally bounded Borel function with the variance asymptotic on a band containing theta satisfies the first-moment interface with zero kernel. Cauchy–Schwarz bounds each first absolute normalized moment by the square root of the uniform second-moment bound. Choosing the continuous weight u to the power (1-theta)/2 in the uniform weighted limit supplies the mixed first-moment limit."))),
                DescribeRole.Theorem))));
}
