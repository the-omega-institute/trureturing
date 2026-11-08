using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MomentTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed increment moment limits transfer to the original price-weighted response for every real integrable profile.",
        H("Moment transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moment-transfer"),
                DeclarationHandle.Create(Prefix + "moment_transfer"),
                H("Moment transfer for every positive integer order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix 0<theta<1 and a positive integer k. Suppose E is measurable and "
                        + "bounded on compact intervals, the integrals of |B(s,x)|^k against the "
                        + "dyadic logarithmic probability measure are eventually bounded by one "
                        + "constant C uniformly for 0<=s<=1, and the position-weighted mixed moments "
                        + "converge pointwise on the unit cube to a measurable function M. Then for "
                        + "every real L1 profile g, the kth moment of the original normalized "
                        + "price-weighted response converges to the integral of product_i g(s_i)*M(s) "
                        + "over the k-dimensional unit cube.")),
                    Paragraph(Text(
                        "Expand the kth power by integral_fintype_prod_eq_pow and apply Fubini. "
                        + "Generalized Holder, using ENNReal.lintegral_prod_norm_pow_le, bounds the "
                        + "absolute mixed increment moment by 2^(k*r)*C. Replacing each normalized "
                        + "price factor by one changes the profile moment by at most "
                        + "((1+eta(X))^k-1)*2^(k*r)*C*||g||_1^k, which tends to zero. "
                        + "The remaining cube integral converges by dominated convergence, with "
                        + "integrable majorant 2^(k*r)*C*product_i |g(s_i)|."))),
                DescribeRole.Theorem))));
}
