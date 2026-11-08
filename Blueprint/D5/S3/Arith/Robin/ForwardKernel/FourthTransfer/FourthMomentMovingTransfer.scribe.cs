using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FourthMomentMovingTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentMovingTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local fourth energy transfers interval-weighted fixed-scale mixed moments to moving lengths.",
        H("Moving-length mixed moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-mixed-moments-tendsto"),
                DeclarationHandle.Create(Prefix + "moving_mixed_moments_tendsto"),
                H("Fixed-scale to moving-length transfer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be measurable and locally bounded, let 0<alpha<theta<beta<1, "
                        + "and assume the local fourth-energy estimate with constant C. "
                        + "For an integer 0<k<=4, suppose the fixed-scale interval-weighted "
                        + "mixed moments converge to a continuous kernel W. Let each length "
                        + "b_i on [1,2] be continuously differentiable, lie between zero "
                        + "and M with M>=1, and have derivative bounded in absolute value "
                        + "by L>=0. For every real continuous weight w on [1,2], the dyadic "
                        + "expectation of w(x/X) times the product of "
                        + "D_{X^theta b_i(x/X)}(x)/sqrt(X^theta log X) converges to "
                        + "the integral of w(u) W((b_i(u))_i) against du/(u log 2).")),
                    Paragraph(Text(
                        "Freeze all lengths and the weight at the left endpoints of n "
                        + "equal cells. Uniform fourth moments and the telescoping product "
                        + "bound control length replacement by a constant times the fourth "
                        + "root of the freezing error. The latter is bounded eventually "
                        + "by freezeCoefficient(C,L,n)+1/n^2 and tends to zero as n grows. "
                        + "Uniform continuity controls weight replacement. For fixed n, "
                        + "the assumed interval moments give the limit of the finite "
                        + "block sum; exact logarithmic cell masses then give the limiting "
                        + "integral as n tends to infinity. Shared endpoints have measure "
                        + "zero. Neither a second-order variance asymptotic nor a special "
                        + "formula for W is required."))),
                DescribeRole.Theorem))));
}
