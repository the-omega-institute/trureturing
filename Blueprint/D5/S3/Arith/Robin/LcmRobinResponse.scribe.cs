using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LcmRobinResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LcmRobinResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative Mertens response gives a strict Robin violation at the actual prefix lcm.",
        H("Robin response of the actual lcm"),
        Blocks(
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
