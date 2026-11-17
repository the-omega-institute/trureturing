using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CommonBandCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CommonBandCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform common-band covariance.",
        H("Uniform common-band covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-band-covariance-bound"),
                DeclarationHandle.Create(Prefix + "common_band_covariance_bound"),
                H("Uniform common-band covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable and satisfy the cumulative variance band asymptotic on 0<alpha<a<b<beta<1. One positive constant and one eventual threshold control every s,t in [0,1] and every interval [l,r] contained in [X,2X]: the absolute integral of D_(s*x^a)E(x)*D_(t*x^b)E(x) is at most C*X*X^a*log(X)*(1+(b-a)*log(X))^2. Write E as the residual at scale X^a, the terminal double average at a dyadic scale between X^b and 2X^b, and the intervening smoothing blocks. Bound the two residual pairings, the terminal term, and each block pair separately, then sum the quadratic number of pairs. All shifted function norms use containing intervals; the constants do not depend on the interval or profile parameters."))),
                DescribeRole.Theorem))));
}
