using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class WeightRemovalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Von Koch control removes the price weight from the forward kernel.",
        H("Removing the price weight"),
        Blocks(
            Paragraph(Text(
                "Write E(x)=psi(x)-x, H(x)=x^(4/5), and "
                + "T0(x)=sqrt(x)/H(x)^2 times the integral of E(x+u)-E(x) "
                + "over 0<=u<=H(x). Assume the von Koch bound "
                + "|E(x)|<=C*sqrt(x)*log(x)^2 for all sufficiently large x.")),
            Describe.Lean(
                DescribeId.Create("discrepancy-increment-von-koch-bound"),
                DeclarationHandle.Create(Prefix + "discrepancy_increment_vonKoch_bound"),
                H("Uniform increment bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is C>0 such that, for all sufficiently large x and "
                    + "every u in [0,H(x)], |E(x+u)-E(x)| is at most "
                    + "C*sqrt(x)*log(x)^2. Indeed x<=x+u<=2*x, so the "
                    + "von Koch bounds at x and x+u have the same order, "
                    + "uniformly in u."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-weight-removal"),
                DeclarationHandle.Create(Prefix + "forward_kernel_weight_removal"),
                H("Pointwise weight removal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The difference between the weighted response T(x) and "
                    + "T0(x) is O(log(x)^2). Subtract the two defining integrals "
                    + "and bound the price ratio error by 4*x^(-1/5). "
                    + "The uniform increment bound then gives "
                    + "sqrt(x)/H(x)^2 * H(x) * C*sqrt(x)*log(x)^2 "
                    + "* 4*x^(-1/5) = 4*C*log(x)^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-weight-removal-l2"),
                DeclarationHandle.Create(Prefix + "forward_kernel_weight_removal_l2"),
                H("Negligible squared error on dyadic intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of (T(x)-T0(x))^2/x over [X,2X], divided "
                    + "by X^(1/5)*log(X), tends to zero. If the pointwise "
                    + "error is at most K*log(x)^2, then log(x)<=2*log(X) "
                    + "and x>=X bound this integral by 16*K^2*log(X)^4. "
                    + "After division the bound is "
                    + "16*K^2*log(X)^3/X^(1/5), which tends to zero."))),
                DescribeRole.Theorem))));
}
