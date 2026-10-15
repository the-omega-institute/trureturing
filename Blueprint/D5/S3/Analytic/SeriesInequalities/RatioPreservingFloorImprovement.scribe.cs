using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class RatioPreservingFloorImprovementDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/SeriesInequalities/RatioPreservingFloorImprovement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One summable floor has arbitrarily small mass, preserves an adjacent ratio "
        + "bound, and improves every fixed near-critical numerical profile.",
        H("Ratio Preserving Floor Improvement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ratio-preserving-floor-improvement"),
                DeclarationHandle.Create(Module + "exists_ratio_preserving_improvement"),
                H("A common floor with small mass and arbitrary tail amplification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let eta be a strictly positive, nonincreasing, summable real sequence "
                        + "on the natural numbers, indexed from zero. Let R>=1 and suppose "
                        + "eta(k)<=R eta(k+1) at every index. For every epsilon>0 there is a "
                        + "single strictly positive, nonincreasing, summable sequence theta "
                        + "whose total sum and every entry are at most epsilon and whose "
                        + "adjacent ratio obeys theta(k)<=R theta(k+1) with the same R.")),
                    Paragraph(Text(
                        "There is a constant c0>0 with c0 eta(k)<=theta(k) at every index. "
                        + "For every real B>0 there is a natural L such that "
                        + "B eta(k)<=theta(k) for all k>=L. The sequence theta is chosen "
                        + "before B, so these tail inequalities hold for every fixed "
                        + "amplification factor on the same sequence.")),
                    Paragraph(Text(
                        "For a natural threshold N, cap the original sequence by "
                        + "f_N(k)=min(eta(k),eta(N)). Dominated convergence makes the total "
                        + "mass of f_N tend to zero as N tends to infinity. Choose thresholds "
                        + "N(j) whose row masses are at most (epsilon/2) 2^(-j), and put "
                        + "theta(k)=sum over j>=0 of f_N(j)(k). Nonnegative double summation "
                        + "gives summability and total mass at most epsilon. Every cap "
                        + "preserves the adjacent ratio bound, so their sum does too.")),
                    Paragraph(Text(
                        "The first cap gives c0=eta(N(0))/eta(0)>0. Beyond the maximum "
                        + "of the first J thresholds, all J corresponding caps equal "
                        + "eta(k), hence theta(k)>=J eta(k). This proves arbitrary tail "
                        + "amplification without requiring the thresholds to increase "
                        + "strictly or asserting pointwise domination of eta everywhere."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-floor-power-profile-improvement"),
                DeclarationHandle.Create(Module + "exists_uniform_profile_improvement"),
                H("Uniform control of all weighted power profiles on an exponent interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same assumptions, with epsilon<=1, one theta has all "
                        + "the preceding floor properties and the following uniform bound. "
                        + "Define P(f,w,s) as the supremum over natural k of "
                        + "ENNReal.ofReal(w(k) f(k)^(-s)); this supremum may be infinite. "
                        + "For all real a and sLo with 0<sLo<=a, and every H>=1, there is "
                        + "C>0 such that for every s in [sLo,a] and every real weight "
                        + "sequence satisfying 0<=w(k)<=1, "
                        + "P(theta,w,s)<=max(ENNReal.ofReal(C), "
                        + "ENNReal.ofReal(H^(-sLo)) P(eta,w,s)).")),
                    Paragraph(Text(
                        "Theta precedes a, sLo and H. The constant C may depend on those "
                        + "parameters and theta, but precedes both s and w. Choose L from "
                        + "the tail amplification by H and take "
                        + "C=1+sum over k<L of theta(k)^(-a). Since theta(k)<=1, this "
                        + "finite prefix controls every s<=a. On the tail, "
                        + "theta(k)>=H eta(k) supplies the factor H^(-sLo) for every "
                        + "s>=sLo. No finiteness assumption on P(eta,w,s) is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-near-critical-floor-profile-improvement"),
                DeclarationHandle.Create(Module + "exists_strict_profile_improvement"),
                H("One floor strictly improves every eventually finite near-critical profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same assumptions including epsilon<=1, one theta has "
                        + "all the preceding floor properties and works for every fixed "
                        + "real sequence n with n(k)>=1 and every real a>0. Define "
                        + "G(f,n,a,u)=P(f,k maps to n(k)^(-u),a-u). If G(eta,n,a,u) "
                        + "is finite for all sufficiently small positive u, then "
                        + "G(theta,n,a,u) is also eventually finite, the real value of "
                        + "G(eta,n,a,u) is eventually positive, and "
                        + "G(theta,n,a,u).toReal/G(eta,n,a,u).toReal tends to zero "
                        + "as u tends to zero from above. Theta is chosen before n and a.")),
                    Paragraph(Text(
                        "Summability and positivity force eta(k) to tend to zero. "
                        + "Consequently eta(k)^(-a) tends to infinity. For each fixed k, "
                        + "the corresponding near-critical term tends to eta(k)^(-a), "
                        + "so the real old profile tends to infinity whenever it is "
                        + "eventually finite. Apply the uniform bound with sLo=a/2: "
                        + "the finite-prefix term divided by the old profile vanishes, "
                        + "and H^(-a/2) can be arbitrarily small.")),
                    Paragraph(Text(
                        "These are numerical supremum statements. They supply no "
                        + "comparison with the moments of an actual sampling strategy "
                        + "or with its actual reference expenditure. A common sufficient "
                        + "sum budget K can be retained by choosing epsilon<=min(1,K); "
                        + "a separate bridge is required to infer actual moment improvement."))),
                DescribeRole.Theorem))));
}
