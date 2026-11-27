using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class RobinEffectiveAbelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Abel summation and weighted Chebyshev tails for the effective Robin bound.",
        H("Abel summation for the effective Robin bound"),
        Blocks(
            Paragraph(Text("The prime reciprocal-square sum uses the real cutoffs a and z, with primes strictly above a and at most z. This matches the actual arithmetic surplus at a = √(2z).")),
            Describe.Lean(DescribeId.Create("finite-abel"), DeclarationHandle.Create(Prefix + "finite_theta_abel"),
                H("Exact finite Abel summation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 1 < a ≤ z, the sum of 1/p² over primes in (a,z] is θ(z)/(z² log z) − θ(a)/(a² log a) plus the interval integral of θ against the weight of order 2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integrated-root"), DeclarationHandle.Create(Prefix + "integrated_root"),
                H("Weighted integral at a prime-power root"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real j > 1, k ≥ 1 and x > 1, the order-j weighted tail of ψ(t^(1/k)) is B(j,1/k,log x) plus J(kj,x^(1/k))/k, where B integrates the real power term and J is the native centered Chebyshev tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-lower"), DeclarationHandle.Create(Prefix + "theta_abel_from_tails"),
                H("Lower bound for the prime sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 1 < a ≤ z, the same prime sum is at least T(2,a) − T(2,z) − log(4)/(a log a), where T is the weighted θ tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-root"), DeclarationHandle.Create(Prefix + "normalized_root_bound"),
                H("Normalized root correction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume every actual zero occurrence has real part 1/2. For real 1 ≤ k ≤ 5 and u > 0 with u/k ≥ log 2, u exp(3u/2) times the sum of B(2,1/k,u) and J(2k,exp(u)^(1/k))/k is at most 2 exp((1/k − 1/2)u)/(2 − 1/k) + (k/20)(2 + 1/u) exp((1/(2k) − 1/2)u)."))), DescribeRole.Theorem)
        )));
}
