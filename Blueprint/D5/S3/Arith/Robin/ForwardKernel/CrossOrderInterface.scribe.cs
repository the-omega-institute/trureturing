using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CrossOrderInterfaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the two variance band asymptotics with a<b, every continuous real function phi on [1,2] satisfies uniform convergence to zero of the dyadic expectation of phi(x/X) B_a(s,x) B_b(t,x). The two second moment bounds control absolute logarithmic mass, and continuous weight approximation extends uniform subinterval cancellation to phi.",
        H("Uniform continuous weighted cross moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cross-interval-cancellation"),
                DeclarationHandle.Create(Prefix + "cross_interval_cancellation"),
                H("Uniform cross interval cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a<b lie in two valid variance bands for the same locally bounded Borel function. The integral of D_(s*x^a)(x) D_(t*x^b)(x) over any subinterval of [X,2X], divided by X^(1+(a+b)/2) log(X), tends to zero uniformly over s,t in [0,1] and both endpoints. Intermediate powers X^mu and X^nu inside the first variance band and below b make each of the three ratios in the four-scale covariance bound tend to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-weighted-interval-cancellation"),
                DeclarationHandle.Create(Prefix + "cross_weighted_interval_cancellation"),
                H("Normalized cross moments on subintervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the same two bands and a<b, the integral of B_a(s,x) B_b(t,x)/x tends to zero uniformly over both time parameters and all dyadic subintervals. The reciprocal weight is x^(-1-(a+b)/2)/log(x), and the shared decreasing-weight estimate transfers the raw interval bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-moment-uniform"),
                DeclarationHandle.Create(Prefix + "cross_moment_uniform"),
                H("Uniform continuous weighted cross moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the two variance band asymptotics with a<b, every continuous real function phi on [1,2] satisfies uniform convergence to zero of the dyadic expectation of phi(x/X) B_a(s,x) B_b(t,x). The two second moment bounds control absolute logarithmic mass, and continuous weight approximation extends uniform subinterval cancellation to phi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-moment-interface"),
                DeclarationHandle.Create(Prefix + "cross_moment_interface"),
                H("The cross-moment interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two variance bands containing a<b, the joint first-first interface has identically zero kernel. The larger of the two uniform second absolute-moment bounds controls both exponents. Choosing the continuous weight u to the power (1-a)/2+(1-b)/2 in the weighted cross limit gives the mixed-moment limit at every point of the closed unit square."))),
                DescribeRole.Theorem))));
}
