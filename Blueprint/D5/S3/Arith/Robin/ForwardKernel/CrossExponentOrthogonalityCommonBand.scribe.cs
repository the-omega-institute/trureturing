using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CrossExponentOrthogonalityCommonBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonalityCommonBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cross-exponent profile orthogonality on a common band.",
        H("Cross-exponent profile orthogonality on a common band"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-cross-exponent-common-band"),
                DeclarationHandle.Create(Prefix + "profile_cross_exponent_common_band"),
                H("Cross-exponent profile orthogonality on a common band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable, and suppose the cumulative variance band asymptotic holds on 0<alpha<a<b<beta<1. For every pair of real integrable profiles g1,g2 on [0,1], the absolute cross integral of their moving profile responses against dx/x on [X,2X] is at most C*||g1||1*||g2||1*X^(1-b)*log(X)*(1+(b-a)*log(X))^2. The constant and the eventual threshold are independent of both profiles, including zero and sign-changing profiles. Apply the uniform common-band covariance estimate to the weighted profile integral formula and use X^(-a-b)*X*X^a=X^(1-b). Relative to the geometric mean of the two individual mean-square scales, this gives a bound of order X^(-(b-a)/2)*log(X)^2; it is a second-moment estimate and does not assert independence."))),
                DescribeRole.Theorem))));
}
