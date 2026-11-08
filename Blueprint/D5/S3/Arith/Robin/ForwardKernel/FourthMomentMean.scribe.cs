using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short averages control the first moment of a moving price-weighted profile.",
        H("Vanishing normalized first moment"),
        Blocks(
            Paragraph(Text(
                "Let E be locally bounded and measurable, and assume the cumulative variance "
                + "asymptotic uniformly in an exponent band 0<alpha<theta<beta<1. "
                + "Fix theta<nu<beta, put M=X^nu, and let g be a real integrable profile on (0,1).")),
            Describe.Lean(
                DescribeId.Create("profile-response-mean-bound"),
                DeclarationHandle.Create(Prefix + "profile_response_mean_bound"),
                H("Quantitative first-moment bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a constant C>0 such that, for all sufficiently large X, "
                        + "the absolute value of the integral of profileResponse(E,theta,g,x)/x "
                        + "over [X,2X] is at most C times the L1 norm of g times sqrt(log X) "
                        + "times (X^((1-nu)/2)+X^((nu-theta)/2)).")),
                    Paragraph(Text(
                        "For f_s(x)=E(x+s*x^theta)-E(x), the short-average estimate and "
                        + "the moving-increment square bound on [X,3X] give a uniform primitive "
                        + "bound sqrt(log X) times (X^(1+theta-nu/2)+X^((1+theta+nu)/2)). "
                        + "The endpoint-strip comparison is the constant-second-function case "
                        + "of FourScaleCovariance.covariance_of_norm_bounds. For the price "
                        + "weight use ProfileCrossIntegral.crossWeight with exponents theta "
                        + "and 1/2 and second parameter zero. Its existing smoothness and "
                        + "variation estimate give total variation including the right endpoint "
                        + "at most (27+theta+1/2)*X^(-theta-1/2). "
                        + "WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound "
                        + "then gives the bound for each s. Local boundedness of E and "
                        + "integrability of g justify Fubini and the final L1 estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-response-mean-tendsto-zero"),
                DeclarationHandle.Create(Prefix + "profile_response_mean_tendsto_zero"),
                H("The normalized mean tends to zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of profileResponse(E,theta,g,x)/x over [X,2X], divided "
                    + "by sqrt(X^(1-theta)*log X), tends to zero as X tends to infinity. "
                    + "Dividing the quantitative bound by this square root leaves a constant "
                    + "times X^(-(nu-theta)/2)+X^(-(1-nu)/2), and both terms tend to zero. "
                    + "The statement concerns the normalized first moment."))),
                DescribeRole.Theorem))));
}
