using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LcmRobinResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LcmRobinResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative Mertens response gives a strict Robin violation at the actual prefix lcm.",
        H("Robin response of the actual lcm"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-cutoff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/LcmRobinResponse.primeCutoff"), H("The finite prime cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff consists of the positive natural primes at most floor(u). It is the exact support of the lcm Euler-tail estimate reused in the quantitative Mertens residual comparison."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("omitted-lcm-factor"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/LcmRobinResponse.tailFactor"), H("The first omitted lcm Euler factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real cutoff u and natural p, tailFactor(u,p)=1/p^(Nat.log(p,floor(u))+1). On the prime cutoff it is the first power omitted by the prefix least common multiple. The quantitative Mertens residual comparison uses this exact exponent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lcm-euler-tail-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/LcmRobinResponse.lcm_tail_bound"), H("A square-root bound on the omitted lcm Euler tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real u>=10000, the sum over p<=u of -log(1-tailFactor(u,p)) is at most 4/sqrt(u). Splitting primes at sqrt(u) bounds the small-prime factors by 1/u and the large-prime factors by 1/p^2. The quantitative Mertens proof uses the bound to control the complete omitted prime-power residual."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-robin-response"),
                DeclarationHandle.Create(Prefix + "common_robin_response"),
                H("Strict Robin violation from a negative Mertens response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real u>=10000, if Mertens.E₃(u)<-4/sqrt(u)-(psi(u)-u)/(u*log(u)), "
                        + "then D=Nat.lcmUpto floor(u) satisfies divisorRatio(D)>exp(gamma)*log(log(D)), "
                        + "5040<D, log(D)=psi(u), and D<=exp(u*log(u)). Here gamma is the real Euler "
                        + "constant and divisorRatio(D)=sigma(1,D)/D.")),
                    Paragraph(Text(
                        "At price zero, golden_resource_objective_factorization and golden_resource_sigma_identity "
                        + "express log(sigma(D)/D) as the sum of local logarithms. Mathlib's factorization_lcmUpto "
                        + "and primeFactors_lcmUpto identify the actual exponents and prime support. Expanding "
                        + "Mertens.E₃ leaves the sum of logarithmic tails. For p<=sqrt(u) the tail factor is below "
                        + "1/u; for p>sqrt(u) it is at most 1/p^2. The shared quadratic logarithm bound and "
                        + "Mertens.sum_one_div_sq_le bound the total by 4/sqrt(u).")),
                    Paragraph(Text(
                        "The strict tangent loglog_tangent supplies the non-strict tangent bound by treating "
                        + "u=psi(u) separately. If D satisfied the weak Robin inequality, logarithmic monotonicity "
                        + "would force Mertens.E₃(u)>=-4/sqrt(u)-(psi(u)-u)/(u*log(u)), contradicting the premise. "
                        + "Mathlib's psi_eq_log_lcmUpto, endpoint divisibility, and Chebyshev's psi bound give "
                        + "the three accompanying witness facts."))),
                DescribeRole.Theorem))));
}
