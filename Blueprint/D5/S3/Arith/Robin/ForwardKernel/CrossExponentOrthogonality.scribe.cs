using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CrossExponentOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate variance bands yield a power saving for cross integrals of price-weighted moving profiles.",
        H("Cross-exponent orthogonality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-cross-exponent-two-bands"),
                DeclarationHandle.Create(Prefix + "profile_cross_exponent_two_bands"),
                H("Two-band power saving"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be locally bounded and measurable, with variance "
                        + "band asymptotics on 0<alpha1<a<beta1<1 and "
                        + "0<alpha2<b<beta2<1, where a<b. Fix "
                        + "a<mu<nu<min(beta1,b) and set "
                        + "eta=min(mu-a,nu-mu,b-nu)/2. There is C>0 and one "
                        + "eventual threshold, both independent of the real "
                        + "integrable profiles g1,g2, such that the absolute "
                        + "integral of profileResponse(E,a,g1,x) times "
                        + "profileResponse(E,b,g2,x) with respect to dx/x over "
                        + "[X,2*X] is at most "
                        + "C*profileL1(g1)*profileL1(g2)*"
                        + "X^(1-(a+b)/2)*log(X)*X^(-eta). "
                        + "Zero profiles are included.")),
                    Paragraph(Text(
                        "TranslationStripBounds.comparableLengthVarianceUpper_of_band "
                        + "supplies the scales X^a, X^mu and X^nu from the first "
                        + "band and X^b from the second. Apply "
                        + "FourScaleCovariance.four_scale_covariance_bound. "
                        + "Each square-root scale ratio is at most X^(-eta). "
                        + "ProfileCrossIntegral.profile_cross_integral_of_covariance_bound "
                        + "then transfers the uniform primitive estimate to the "
                        + "actual price-weighted profiles. Its weight factor "
                        + "X^(-a-b) combines with X*sqrt(X^a*X^b) to give "
                        + "X^(1-(a+b)/2)."))),
                DescribeRole.Theorem))));
}
