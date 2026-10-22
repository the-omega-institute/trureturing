using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LcmRobinResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LcmRobinResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Mertens third-theorem error controls the Robin response of the actual prefix lcm.",
        H("Robin response of the actual lcm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-robin-response"),
                DeclarationHandle.Create(Prefix + "common_robin_response"),
                H("Common Robin response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real u>=10000, let D=Nat.lcmUpto floor(u). If "
                    + "divisorRatio(D)<=exp(gamma)*log(log(D)), then "
                    + "Mertens.E₃(u)>=-4/sqrt(u)-(psi(u)-u)/(u*log(u)). "
                    + "The proof writes sigma(D)/D as the exact Euler product over primes p<=u, "
                    + "using the lcm factorization and the finite geometric sum for each p-adic layer. "
                    + "The omitted layer contributes at most 4/sqrt(u): primes p<=sqrt(u) have tail below 1/u, "
                    + "and primes p>sqrt(u) have exponent one and are bounded by the reciprocal-square tail. "
                    + "The tangent inequality for log(log) bounds log(log(psi(u))) by its value at u plus "
                    + "(psi(u)-u)/(u*log(u)). Finally psi(u)=log(D), psi(u)<=u*log(u), and the weak Robin "
                    + "inequality is passed through the logarithm; expanding Mertens.E₃ gives the stated bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-robin-response-contrapositive"),
                DeclarationHandle.Create(Prefix + "common_robin_response_contrapositive"),
                H("Strict Robin violation from a negative Mertens response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real u>=10000, if Mertens.E₃(u)<-4/sqrt(u)-(psi(u)-u)/(u*log(u)), "
                    + "then D=Nat.lcmUpto floor(u) satisfies divisorRatio(D)>exp(gamma)*log(log(D)), "
                    + "5040<D, log(D)=psi(u), and D<=exp(u*log(u)). This is the contrapositive of the "
                    + "common response theorem, together with the same lcm logarithm identities and the "
                    + "Chebyshev upper bound used above."))),
                DescribeRole.Theorem))));
}
