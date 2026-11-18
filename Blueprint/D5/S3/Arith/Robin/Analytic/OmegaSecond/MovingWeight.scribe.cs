using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class MovingWeightDocument : IScribeDocumentDefinition
{
    private static Describe D(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact ramp decomposition and smooth branches of the prime weight localized at a moving cutoff.",
        H("Localized prime weight and exact ramp separation"),
        Blocks(
            D("weight", "weight", "Localized weight", "The weight at P,s,t is log(1+exp(-s*abs(log(t/P)))).", DescribeRole.Definition),
            D("remainder", "remainder", "Finite prime remainder", "The remainder is the sum of the localized weight over all primes at most the natural floor of x.", DescribeRole.Definition),
            D("weight-nonneg", "weight_nonneg", "Nonnegative localized weight", "The localized weight is nonnegative for all real P,s,t.", DescribeRole.Theorem),
            D("weight-peak", "weight_le_log_two", "Uniform peak height", "For s>=0 the localized weight is at most log(2), for all real P,t.", DescribeRole.Theorem),
            D("weight-continuous", "weight_continuousOn", "Continuity away from zero", "For P>0 and a>0, the localized weight is continuous on every closed real interval [a,b], for every real s.", DescribeRole.Theorem),
            D("left-weight", "leftWeight", "Smooth left extension", "The left extension subtracts s*(log(P)-log(t)) from log(1+P^s/t^s).", DescribeRole.Definition),
            D("left-equals", "leftWeight_eq_weight", "Left-branch identity", "For P>0,t>0,s>=0,t<=P, the smooth left extension equals the localized weight.", DescribeRole.Theorem),
            D("right-equals", "rightWeight_eq_weight", "Right-branch identity", "For P>0,t>0,s>=0,P<=t, log(1+P^s/t^s) equals the localized weight.", DescribeRole.Theorem),
            D("left-derivative", "leftWeight_deriv", "Left-branch derivative", "For P>0,t>0 and every real s, the left extension has derivative s/t-abelKernel(s,P^s,t).", DescribeRole.Theorem),
            D("left-cutoff", "leftWeight_at_cutoff", "Left endpoint value at the peak", "For P>0 and every real s, the smooth left extension at t=P equals log(2).", DescribeRole.Theorem),
            D("right-cutoff", "rightWeight_at_cutoff", "Right endpoint value at the peak", "For P>0 and every real s, log(1+P^s/P^s) equals log(2).", DescribeRole.Theorem),
            D("left-derivative-nonneg", "leftWeight_deriv_nonneg", "Increasing left branch", "For P>0,t>0,s>=0, the left-branch derivative s/t-abelKernel(s,P^s,t) is nonnegative.", DescribeRole.Theorem),
            D("prime-weight-split", "prime_weight_split", "Exact finite prime ramp decomposition", "For P>0,P<=x,s>=0, the sum over primes p<=x of log(1+P^s*p^(-s)) equals s*(primeCount(P)*log(P)-theta(P))+remainder(P,s,x). The natural-floor endpoints and the prime at the cutoff are retained exactly. This supports an upper bound at the second distinct-prime threshold; a matching lower bound has not been established.", DescribeRole.Theorem))));
}
