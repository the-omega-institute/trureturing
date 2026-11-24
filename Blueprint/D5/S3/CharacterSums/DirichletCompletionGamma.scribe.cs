using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCompletionGammaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Archimedean and arithmetic estimates for Dirichlet logarithmic derivatives.",
        H("Explicit completion estimates"),
        Blocks(
            Describe.Lean(DescribeId.Create("gamma-real-part"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.norm_Gamma_le"),
                H("Vertical Gamma product comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex z with positive real part, norm(Gamma(z)) <= "
                    + "Gamma(Re(z)). The classical vertical product for the squared Gamma norm "
                    + "is Gamma(Re(z)) squared divided by a product whose factors are at "
                    + "least one. Positivity of the real Gamma function gives the norm "
                    + "comparison. Equality occurs on the positive real axis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-convex-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.Gamma_le_max_factorial"),
                H("Convexity and an integer endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every real u at least one quarter, Gamma(u) is at most the maximum "
                    + "of Gamma(1/4) and the factorial of ceiling(u)-1. The point u lies "
                    + "between one quarter and the positive integer ceiling(u). Convexity of real "
                    + "Gamma function bounds its value by the larger endpoint value, and the "
                    + "Gamma value at the integer endpoint is that factorial. The completion "
                    + "and Gamma identities are classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-exponential-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.Gamma_le_exp_bound"),
                H("An explicit Gamma growth estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every real u at least one quarter, Gamma(u) is at most "
                    + "Gamma(1/4) or strictly below exp((u+1) log(u+1)). The factorial "
                    + "contribution is "
                    + "strictly below the exponential because ceiling(u) < u+1 and "
                    + "log(u+1) is positive. The fixed endpoint contribution remains in the "
                    + "first branch, while the second branch retains its strict inequality. "
                    + "This combines the classical convexity and factorial estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-gamma-factor"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.norm_GammaReal_le"),
                H("Deligne real archimedean factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex s with positive real part, norm(GammaReal(s)) <= pi "
                    + "to the power (-Re(s)/2) times Gamma(Re(s)/2). Here GammaReal(s) means "
                    + "pi to the power (-s/2) times Gamma(s/2). The exact norm of the power "
                    + "of the positive real number pi and the vertical Gamma comparison give "
                    + "the bound. The completion and Gamma identities are classical analytic "
                    + "number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("logarithmic-series-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.logarithmic_series_bound"),
                H("A strict bound at exponent two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "The real series with terms log(n)/n squared is summable and its sum "
                    + "is at most log(2)/4 + 4 log(3)/9 + 1/3, which is strictly less than "
                    + "one. Separate the terms n=2 and n=3. On the interval from three to "
                    + "infinity, log(x)/x squared is nonnegative and decreasing, and its "
                    + "integral is (log(3)+1)/3. The classical integral test bounds the "
                    + "remaining tail. The inequalities log(2)<7/10 and log(3)<11/10 prove "
                    + "strictness. The von Mangoldt coefficients are bounded by log(n), "
                    + "so this estimate controls Dirichlet logarithmic derivatives on the "
                    + "vertical line of real part two."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("digamma-height-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.digamma_re_lt_log_height"),
                H("Binet remainder on a Gamma strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex z with 1 <= Re(z) <= 3/2, the real part of "
                    + "digamma(z) is at most log(2 abs(Im(z))+3)-log(2)+1/2-Re(1/(2z)). Binet's "
                    + "formula bounds the remainder after log(z)-1/(2z) by 1/(2 Re(z)). "
                    + "The real part of 1/(2z) is nonnegative and 1/(2 Re(z)) <= 1/2. "
                    + "The estimate 2 norm(z) <= 2 abs(Im(z))+3 and log(2)>1/2 absorb "
                    + "the remainder while retaining both correction terms. This is a "
                    + "consequence of the classical "
                    + "Binet formula for the logarithmic derivative of Gamma."))),
                DescribeRole.Theorem))));
}
