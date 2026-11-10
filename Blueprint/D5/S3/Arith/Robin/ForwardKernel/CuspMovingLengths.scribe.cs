using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CuspMovingLengthsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CuspMovingLengths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving lengths and power weights preserve the clipped cusp cross energy.",
        H("Moving cusp lengths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-cusp-energy"),
                DeclarationHandle.Create(Prefix + "movingCuspEnergy"),
                H("Moving cusp cross energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moving cusp energy integrates (X+y)^(-a-b) times the cusp averages of lengths (X+y)^a and (X+y)^b over 0<=y<=X^b, using clipping radii X^a and X^b."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "Write B_q(y) for the averaged forward increment of the clipped logarithm with radii 0<h<k, "
                + "L=log(k/h), and E for the integral of B_h(y)B_k(y) over [0,k]. "
                + "For y>=h, CuspAverages.cuspAverage_length_comparison gives "
                + "B_r(y)<=B_q(y)<=(q/r)B_r(y) whenever 0<r<=q. "
                + "The interval below h is estimated separately because lower clipping prevents concavity there.")),
            Describe.Lean(
                DescribeId.Create("power-length-relative-bounds"),
                DeclarationHandle.Create(Prefix + "power_length_bounds"),
                H("Relative bounds for power lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0, 0<=theta<=1 and 0<=y<=k, the power (X+y)^theta lies between X^theta and X^theta(1+k/X)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-cusp-average-continuous"),
                DeclarationHandle.Create(Prefix + "power_average_continuous"),
                H("Continuity with a power length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k and theta>=0, the function y mapping to the cusp average with length (X+y)^theta and base y is continuous on the real line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-cross-energy-weighted-moving-lengths"),
                DeclarationHandle.Create(Prefix + "cuspCrossEnergy_weighted_moving_lengths"),
                H("Simultaneous length and weight transport"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 0<=delta<=1, epsilon>=0 and W>=0. Suppose h<=q1(y)<=h(1+delta), "
                    + "k<=q2(y)<=k(1+delta), and 0<=w(y)<=W with w(y)>=(1-epsilon)W on [0,k]. "
                    + "If the moving weighted product is interval integrable, its integral differs from W*E "
                    + "by at most (3*delta+epsilon)*W*E+2*W*h*L. "
                    + "Above h the moving product lies between the frozen product and (1+delta)^2 times it. "
                    + "Below h each product is between zero and 2L. "
                    + "The estimate supplies the power-weight calculation and CommonBandSharpnessTransport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-cusp-energy-estimate"),
                DeclarationHandle.Create(Prefix + "movingCuspEnergy_estimate"),
                H("Power lengths and the original power weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<a<b<1 there is C>0 such that, for all sufficiently large X, "
                    + "putting h=X^a, k=X^b and L=log(k/h), the integral of "
                    + "(X+y)^(-a-b)*B_((X+y)^a)(y)*B_((X+y)^b)(y) over [0,k] "
                    + "differs from X^(-a-b)*h*L^2/4 by at most "
                    + "C*X^(-a-b)*(h*L+(k/X)*h*L^2). "
                    + "The power lengths lie in their relative k/X intervals. The power weight lies "
                    + "between (1-2k/X)*X^(-a-b) and X^(-a-b). Continuity gives the required integrability. "
                    + "Combining simultaneous transport with CuspCrossEnergy.cuspCrossEnergy_estimate "
                    + "gives the two errors used by CommonBandSharpnessTransport."))),
                DescribeRole.Theorem))));
}
