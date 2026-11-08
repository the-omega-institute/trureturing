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
                DescribeId.Create("joint-moment-transfer"),
                DeclarationHandle.Create(Prefix + "joint_moment_transfer"),
                H("Joint moment transfer for a finite family of profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive integer k, exponents e_i strictly between zero and one, "
                        + "and real integrable profiles G_i. If E is measurable and bounded on compact "
                        + "intervals, the absolute kth moments of the normalized increments are "
                        + "eventually uniformly bounded over every index and unit parameter, and "
                        + "the joint position-weighted mixed moments converge at every point of the "
                        + "unit cube to M, then the moment of the product of normalized profile "
                        + "responses converges to the cube integral of product_i G_i(s_i) times M(s).")),
                    Paragraph(Text(
                        "Expand the finite product of profile integrals and apply Fubini. "
                        + "Generalized Holder bounds the absolute mixed increment moment by "
                        + "2 raised to the sum of r(e_i), times the common moment bound. Apply the "
                        + "price estimate to each exponent and sum their absolute errors to obtain "
                        + "one vanishing error bound. Replacing all price factors by one has "
                        + "vanishing integral error; dominated convergence gives the remaining limit. "
                        + "Only measurability of the approximating kernels is needed."))),
                DescribeRole.Theorem),
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
                        "Apply joint moment transfer to the constant exponent and constant profile "
                        + "families. Their joint increment moments equal the original mixed moments, "
                        + "and the product of normalized responses is the kth power."))),
                DescribeRole.Theorem))));
}
