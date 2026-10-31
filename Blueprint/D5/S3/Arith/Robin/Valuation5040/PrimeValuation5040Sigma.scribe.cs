using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Valuation5040;

internal sealed class PrimeValuation5040SigmaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 5040 valuation fibre contributes an exact normalized divisor-sum factor.",
        H("The 5040 valuation sigma factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sigma-5040-coprime-factor"),
                DeclarationHandle.Create(Prefix + "sigma_5040_mul_of_coprime"),
                H("Raw divisor-sum factorization"),
                StatementSource.FromAuthor(Disp(F.Id("sigma5040MulOfCoprime"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If n is coprime to 210, multiplicativity gives sigma(5040 n) "
                        + "= 19344 sigma(n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-sigma-5040-coprime-factor"),
                DeclarationHandle.Create(Prefix + "normalized_sigma_5040_mul_of_coprime"),
                H("Normalized 5040 factorization"),
                StatementSource.FromAuthor(Disp(F.Id("normalizedSigma5040MulOfCoprime"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonzero residual n coprime to 210, the normalized ratio splits as "
                        + "sigma(5040 n)/(5040 n) = (403/105) sigma(n)/n.")),
                    Paragraph(Text(
                        "Under exactly these hypotheses, put r = sigma(n)/n. Since 403/105 "
                        + "is positive, the factorization gives sigma(5040 n)/(5040 n) > 2 "
                        + "if and only if r > 2*(105/403) = 210/403. This is an application "
                        + "of normalized_sigma_5040_mul_of_coprime and ordered-field arithmetic; "
                        + "it preserves the nonzero and coprime-to-210 assumptions.")),
                    Paragraph(Text(
                        "The strict threshold equivalence is an exact rescaling and supplies "
                        + "no upper bound for the residual ratio. The conditional ordered bound "
                        + "below still requires its separate bound B for every positive residual "
                        + "m coprime to 210 satisfying AllowedOrdered 210 m. Neither the "
                        + "threshold equivalence nor the finite factor supplies that bound, "
                        + "a Robin inequality, or an RH implication."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-sigma-5040-fibre"),
                DeclarationHandle.Create(Prefix + "normalized_sigma_of_jointFiber5040"),
                H("Normalized factor on the exact valuation fibre"),
                StatementSource.FromAuthor(Disp(F.Id("normalizedSigmaOfJointFiber5040"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The 5040 joint-fibre hypotheses supply the residual nonzeroness and "
                        + "coprimality, so the same exact factorization applies on the fibre."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-sigma-5040-ordered-bound"),
                DeclarationHandle.Create(Prefix + "normalized_sigma_of_jointFiber5040_le_of_ordered_bound"),
                H("Conditional Robin reduction on the 5040 fibre"),
                StatementSource.FromAuthor(Disp(F.Id("normalizedSigmaOfJointFiber5040LeOfOrderedBound"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any upper bound B for normalized sigma on positive ordered residuals "
                        + "propagates to the joint fibre with the multiplicative factor 403/105."))),
                DescribeRole.Theorem))));
}
