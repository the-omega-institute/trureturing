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
                        "The universal integer envelope 0<=d(k)<=delta k^8 is an explicit " +
                        "premise. The resulting estimate is 4 delta^2 s^2 min(1,(sL)^8). " +
                        "This specialization retains both the universal envelope and the " +
                        "factorial-normalizer inequality as premises. The source-neighborhood " +
                        "application of the existing scaled power-sum limit is a separate bridge. " +
                        "Every finite cutoff is covered under the same stated premises, including " +
                        "cutoffs depending on s or q."))),
                DescribeRole.Theorem))));
}
