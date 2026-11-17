using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class MSConjectureOscillationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureOscillation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second and fourth Montgomery–Soundararajan conjectural moments imply two-sided positive-proportion oscillation for every nonzero real integrable moving profile.",
        H("Conditional arithmetic profile oscillation"),
        Blocks(
            Paragraph(Text(
                "Montgomery and Soundararajan, Primes in short intervals, Communications in Mathematical Physics 252 (2004), 589–617, "
                + "Conjecture 1, is assumed only for K=2 and K=4. Its constants are mu_2=1 and mu_4=3. "
                + "For each fixed epsilon>0 the relative moment error tends to zero uniformly over integer lengths "
                + "(log N)^(1+epsilon)<=H<=N^(1-epsilon). No correlation estimate, Riemann hypothesis, or extension of Theorem 3 is assumed. "
                + "The implications for real moving lengths and arbitrary L1 profiles are derived here.")),
            Describe.Lean(
                DescribeId.Create("conjecture-implies-variance-and-fourth-bound"),
                DeclarationHandle.Create(Prefix + "conjecture_implies_variance_and_fourth_bound"),
                H("Cumulative variance and fourth moments on every band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MSConjectureTwoFour. For every 0<alpha<beta<1, the complete Chebyshev error E=psi-id satisfies "
                    + "CumulativeVarianceBandAsymptoticFor E alpha beta, and there exists C4 such that FourthMomentBandBoundFor E alpha beta C4. "
                    + "Thus V(Y,u)/(Y u log(Y/u)) tends uniformly to one for Y^alpha<=u<=Y^beta, and the fourth increment integral "
                    + "is uniformly at most C4 Y u^2 log^2(Y/u). Floors of the cutoff and length remain in the conjectural range. "
                    + "The rounded second main term differs by O(Y log Y); the logarithmic pointwise sampling error and the fourth moment "
                    + "bound control the continuous replacement and the terminal cell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ms-conjecture-profile-response-two-sided-positive-proportion"),
                DeclarationHandle.Create(Prefix + "ms_conjecture_profile_response_two_sided_positive_proportion"),
                H("Two-sided positive logarithmic proportions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MSConjectureTwoFour and 0<alpha<theta<beta<1. There exist B>0 and C4>=0 such that for every real "
                    + "Borel representative g integrable on (0,1) that is not almost everywhere zero, put K=B C4 ||g||_1^4, "
                    + "v=(2^(1-theta)-1)Q(g)/2, c=fourthMomentThreshold(v,K), and delta=fourthMomentDensity(v,K). "
                    + "Then K>0 and, for every sufficiently large X, the fourth moment of T(theta,g)/sqrt(S_X) under the "
                    + "probability measure dx/(x log 2) on [X,2X] is at most K; both strict tails "
                    + "T(theta,g)>c sqrt(S_X) and T(theta,g)<-c sqrt(S_X) have measure at least delta. "
                    + "Here S_X=X^(1-theta)log X and Q(g) is the Brownian covariance quadratic form. "
                    + "The constants c and delta are the positive constants of the abstract fourth moment oscillation theorem. "
                    + "The Chebyshev error is locally bounded and Borel measurable, so that theorem applies with no further arithmetic assumption."))),
                DescribeRole.Theorem))));
}
