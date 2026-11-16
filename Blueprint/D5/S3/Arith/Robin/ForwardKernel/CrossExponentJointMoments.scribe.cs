using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CrossExponentJointMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the variance and joint fourth-moment hypotheses, separated exponents have vanishing cross moments and a strictly positive limiting covariance of their squares when neither profile vanishes almost everywhere.",
        H("Cross exponent joint moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-z-first-moment-tendsto-zero"),
                DeclarationHandle.Create(Prefix + "jointZ_first_moment_tendsto_zero"),
                H("Vanishing first cross moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and Borel measurable, with variance-band asymptotics on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. For any two integrable profiles, the dyadic expectation of the normalized product of their profile responses tends to zero. The zero cross-moment interface follows from the two variance bands, and joint moment transfer carries it to the two integrable profile responses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-exponent-kernel-integral-zero"),
                DeclarationHandle.Create(Prefix + "cross_exponent_kernel_integral_zero"),
                H("Vanishing universal cross kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and Borel measurable, with variance-band asymptotics on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. Suppose that for every (s,t) in the closed unit square, the dyadic expectation of U_X^{r_a+r_b} B_{a,X}(s) B_{b,X}(t) tends to M(s,t), where U_X=x/X and r_a=(1-a)/2, r_b=(1-b)/2. Then the integral of g1(s)g2(t)M(s,t) over the unit square is zero for every pair of real integrable profiles. The second-moment bounds of the zero cross-moment interface also bound this proposed kernel. Joint moment transfer identifies its profile integral with the first cross moment, and uniqueness of limits gives zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-exponent-squares-positive-correlation"),
                DeclarationHandle.Create(Prefix + "cross_exponent_squares_positive_correlation"),
                H("Positive correlation of mixed squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and Borel measurable, with variance-band asymptotics and fourth-moment band bounds on bands 0<alpha1<a<beta1<1 and 0<alpha2<b<beta2<1, and assume a<b. For integrable profiles and a Brownian joint fourth-moment interface with bounded measurable cross kernel, the dyadic expectation of the normalized product tends to zero and the mixed square moment tends to the product of the two energies multiplied by the summed macroscopic moment and the two kappa factors. Subtracting the separate second-moment limits yields the covariance constant. Under these hypotheses, the strict macroscopic moment inequality and positivity of both profile energies make this covariance strictly positive whenever neither profile vanishes almost everywhere."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "These are conditional results on abstract interfaces. Nothing here establishes the required interfaces or their conclusions for E = psi - id. The almost-everywhere vanishing of the kernel, Corollary 495.4, and Proposition 495.5 are not formalized here.")))));
}
