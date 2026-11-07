using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class NormalizedPowerPerturbationAllCutoffKLDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized countable power perturbations and every finite collapsed cutoff.",
        H("Normalized power perturbations and all-cutoff relative entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-power-perturbation-all-cutoff-kl"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL.normalized_power_perturbation_all_cutoff_kl"),
                H("Both relative entropy directions for every finite collapsed cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let m be an integer at least four, let 0 <= delta <= 1, and let d(0)=0 " +
                        "with 0 <= d(k) <= delta k^(m-1) for every positive integer k. For s>0, " +
                        "the unnormalized weights are k^m exp(-sk) and (k^m+d(k)) exp(-sk) on " +
                        "positive integers, both zero at zero. Their normalizers Z0 and Z1 are " +
                        "the complete infinite sums. Assume m!/2 <= s^(m+1) Z0.")),
                    Paragraph(Text(
                        "Write p0 and p1 for the normalized laws, epsilon=(Z1-Z0)/Z0, " +
                        "r=1-exp(-s), and w(k)=p1(k)-p0(k). The exact signed difference is " +
                        "w(k)=(d(k)-epsilon k^m) exp(-sk)/Z1. The nonnegativity of d does not " +
                        "fix the sign of w or of a sum of its short coordinates.")),
                    Paragraph(Text(
                        "Absolute convergence permits a one-step shift: R_(m-1) <= r R_m, " +
                        "where R_j is the complete positive-index power-exponential sum. Thus " +
                        "R_(m-2) <= r^2 R_m and 0 <= epsilon <= delta r. For either reference j, " +
                        "the full normalized square energy is summable and at most 4 delta^2 r^2. " +
                        "One may use (a-b)^2 <= 2a^2+2b^2 on the signed numerator, retaining " +
                        "the normalization correction in the second term.")),
                    Paragraph(Text(
                        "For each natural L>=1 the carrier is Option(Fin L). A short symbol " +
                        "some r denotes the physical count r.val+1, while none carries the entire " +
                        "remaining tail k>L. Its mass is 1 minus the sum of these L short masses. " +
                        "For i=false and i=true the bound is KL(a_i || a_(!i)) <= " +
                        "4 delta^2 s^2 min(1,(sL)^(m-1)). Full-law logarithmic sums are absolutely " +
                        "convergent and bounded by the corresponding square energy.")),
                    Paragraph(Text(
                        "The short-cutoff argument sL<=1 bounds the short reference mass by one " +
                        "half using the factorial-normalizer hypothesis. Weighted Cauchy-Schwarz " +
                        "charges the signed short sum against these same reference masses, including " +
                        "the collapsed tail drift. For sL>1 the complete series and same-reference " +
                        "tail Cauchy inequality give the other branch without a lower bound on " +
                        "the tail mass. The normalizers are never truncated.")),
                    Paragraph(Text(
                        "For m>=4, m!>=24. In the short-cutoff branch the reference short mass " +
                        "is at most 2 L^(m+1)/R_m and hence at most one half. The short square " +
                        "energy is at most 4 delta^2 L^(m-1)/R_m, which is at most " +
                        "2 delta^2 s^2 (sL)^(m-1). The signed short sum has square at most " +
                        "the product of that same reference short mass and short energy, so " +
                        "the collapsed energy is at most twice the short energy. For the other " +
                        "branch, finite weighted Cauchy inequalities pass to the complete tail " +
                        "series by convergence; the positive tail denominator may be arbitrarily small.")),
                    Paragraph(Text(
                        "For the degree-nine source, delta=2749658638697/10^24 and " +
                        "d(k)=(55800726477138 k -224986136658885 k^2 +420664314485485 k^3 " +
                        "-540138133491075 k^4 +518234977000797 k^5 -254383031435085 k^6 " +
                        "+77668004560980 k^7 +43377331415040 k^8)/(35*10^24). " +
                        "Put H_c(k)=k^9+d(k), F_0(k)=k^9 and F_1(k)=H_c(k). The source " +
                        "presents the all-integer envelope as a premise; these literal rational " +
                        "coefficients also verify it directly. Write D=35*10^24 and k=n+1 " +
                        "for n>=0. The coefficients of D*d(n+1), in increasing powers of n, are " +
                        "(96238052354395, 662840242292178, 2008375679734515, " +
                        "3502311640703995, 3990084638673735, 3052095443413107, " +
                        "1503858280112895, 424686655881300, 43377331415040). " +
                        "The coefficients of D*(delta*(n+1)^8-d(n+1)) are " +
                        "(0, 107064176542982, 686289786188545, 1887019291142125, " +
                        "2746579026133915, 2337235488433013, 1190807185810165, " +
                        "345217762953860, 52860720939355). All are nonnegative and D>0, " +
                        "so 0<=d(k)<=delta*k^8 for every positive integer k. Also d(0)=0 " +
                        "and 0<delta<1. In particular k^9<=H_c(k)<=(1+delta)*k^9 and " +
                        "1<=H_c(k)/k^9<=1+delta/k; no finite window is used.")),
                    Paragraph(Text(
                        "The original CriticalRenewalSource.scaled_powerSum_limit at m=9 gives " +
                        "s^10*R_9(s) -> 9! as s decreases to zero through positive reals. Since " +
                        "9!/2<9!, an open right neighborhood supplies s0>0 such that " +
                        "9!/2<=s^10*R_9(s) for every 0<s<s0. This is the required " +
                        "factorial-normalizer inequality, derived from the limit rather than " +
                        "assumed at each parameter. The choice of s0 precedes every cutoff, " +
                        "label, budget and observer. The entropy conclusion needs no hypothesis " +
                        "on the renewal mean; if a further argument requires a separate source " +
                        "moment neighborhood, intersect the two source neighborhoods.")),
                    Paragraph(Text(
                        "Apply normalized_power_perturbation_all_cutoff_kl with m=9, the literal " +
                        "d above, and delta=2749658638697/10^24. For q=exp(-s) the weights are " +
                        "exactly F_i(k)*q^k at every positive integer and zero at zero, because " +
                        "exp(-s*k)=exp(-s)^k. Thus Z_i is the full sum over k>=1, " +
                        "p_i(k)=F_i(k)*q^k/Z_i, and p_i(0)=0. These are positive normalized " +
                        "infinite laws, not finite approximations. The conclusion retains " +
                        "absolute convergence and the complete square-energy and logarithmic " +
                        "series in both directions.")),
                    Paragraph(Text(
                        "For every 0<s<s0, simultaneously for every natural L>=1 and i=0,1, " +
                        "KL(a_i^L || a_(1-i)^L)<=4*delta^2*s^2*min(1,(s*L)^8). " +
                        "The symbol some r with r in Fin L means k=r.val+1; none is the " +
                        "entire k>L tail with mass 1-sum_(k=1)^L p_i(k). In particular the " +
                        "signed difference w(k)=(d(k)-epsilon*k^9)*q^k/Z_1, with " +
                        "epsilon=(Z_1-Z_0)/Z_0, keeps its normalization correction and its " +
                        "collapsed tail coefficient -sum_(k=1)^L w(k). This proves the source " +
                        "collapsed-entropy estimate on one source-only neighborhood, including " +
                        "cutoffs depending on s or q and arbitrarily large s*L. It does not " +
                        "supply the source-clipped observer-kernel data-processing bridge, " +
                        "stationary initial comparison, harmonic stopping argument or paid-read " +
                        "converse; those require their own hypotheses and results."))),
                DescribeRole.Theorem))));
}
