using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCompletionGammaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical Dirichlet completion estimates from Euler integrals and reflection.",
        H("Gamma growth estimates"),
        Blocks(
            Describe.Lean(DescribeId.Create("gamma-real-part"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.norm_Gamma_le"),
                H("Euler integral comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex z with positive real part, norm(Gamma(z)) <= "
                    + "Gamma(Re(z)). Take the norm inside the Euler integral on the positive "
                    + "real axis. The norm of x to the power z minus one is x to the power "
                    + "Re(z) minus one. The resulting integral is the real Gamma function. "
                    + "This is the classical Euler-integral comparison. The completion and "
                    + "Gamma identities are classical analytic number theory."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-convex-bound"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletCompletionGamma.Gamma_le_max_factorial"),
                H("Convexity and an integer endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every real u at least one quarter, Gamma(u) is at most the maximum "
                    + "of Gamma(1/4) and the factorial of the natural ceiling of u. The point "
                    + "u lies between one quarter and ceiling(u)+1. Convexity of the real "
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
                      "For every real u at least one quarter, Gamma(u) <= max(1,Gamma(1/4)) "
                    + "exp((u+1) log(u+1)). Bound the ceiling factorial by the ceiling raised "
                    + "to itself, use ceiling(u) <= u+1, and express the resulting power "
                    + "through the real exponential. The fixed endpoint contribution is "
                    + "retained in the multiplicative constant. The completion and Gamma "
                    + "identities are classical analytic number theory."))),
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
                    + "of the positive real number pi and the Euler integral comparison give "
                    + "the bound. The completion and Gamma identities are classical analytic "
                    + "number theory."))),
                DescribeRole.Theorem))));
}
